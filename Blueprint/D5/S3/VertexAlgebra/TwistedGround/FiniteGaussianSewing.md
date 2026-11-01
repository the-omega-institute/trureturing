# Finite Gaussian coefficient sewing

## Abstract

Full finite complex bilinear Gaussian coefficient sewing with the native trace-log normalization.

The finite external and shared mode types may be empty. All coefficients are complex bilinear Gaussian coefficients, with no conjugation. The shared occupation weight is the product of coordinate factorials. External coefficients retain their ordinary coefficient normalization; no external factorial is inserted.

This is classical Gaussian/Bargmann-Fock calculus. The actual Gaussian coefficient is extracted from quadratic(K)^(degree/2)/(degree/2)!, using the existing native polynomial definitions. A fixed external row is represented as a finite polynomial times the shared Gaussian. The proof uses the actual Gaussian annihilation equation and induction in external occupation degree. Its base is the existing principal-block polynomial projection. At every positive step the external multiplicity d_i+1 is divided out, external lowerings reduce degree, and a shared lowering is the original creation shift. The resulting polynomial is finite at every fixed external occupation, independently of the size of the external and mixed matrix blocks.

**Definition 1.1 (Actual finite polynomial insertion).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FiniteGaussianSewing.polynomialGaussian`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/FiniteGaussianSewing.polynomialGaussian` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A polynomial monomial with coefficient c and occupation alpha contributes c times created(alpha,gaussianCoefficient(A)). This is the ordinary coefficient convolution of that monomial with the actual Gaussian. The map is linear in the polynomial.

**Definition 1.2 (Actual block coefficient row).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FiniteGaussianSewing.row`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/FiniteGaussianSewing.row` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At shared occupation n the row with external occupation d is gaussianCoefficient(K,d.sumElim(n)).

**Theorem 1.3 (Finite polynomial bridge for arbitrary external blocks).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FiniteGaussianSewing.row_polynomial`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FiniteGaussianSewing.row_polynomial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every symmetric matrix K on X plus H and every external occupation d, a finite shared polynomial p has polynomialGaussian(K_HH,p)=row(K,d). No norm hypothesis occurs in this algebraic identity. Repeated coordinates and empty types remain included.

**Theorem 1.4 (Actual external row contraction converges absolutely).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FiniteGaussianSewing.row_pair_norm_summable`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FiniteGaussianSewing.row_pair_norm_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For symmetric K on X plus H and L on Y plus H, the actual row contraction is absolutely convergent when only K_HH and L_HH are strict Euclidean contractions. The external and mixed blocks are arbitrary. The two finite polynomial witnesses are obtained from row_polynomial, rather than assumed as certificates.

**Definition 1.5 (Actual two-sided Gaussian insertion moment).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FiniteGaussianSewing.bilinearMoment`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/FiniteGaussianSewing.bilinearMoment` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

H(alpha,beta) is the original bilinear factorial pairing of created(alpha,c_A) with created(beta,c_B). Its recurrence contains the exact coordinate multiplicity beta_i and the lowered occupation beta-e_i, including the zero-coordinate case.

**Theorem 1.6 (Ordered resolvent for actual insertion moments).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FiniteGaussianSewing.bilinearMoment_resolvent_step`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FiniteGaussianSewing.bilinearMoment_resolvent_step` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For symmetric strict shared contractions A and B, set U_i=H(alpha+e_i,beta), V_i=H(alpha,beta+e_i), u_i=beta_i H(alpha,beta-e_i), and v_i=alpha_i H(alpha-e_i,beta). Actual factorial adjointness and absolute summability give U=B V+u and V=A U+v. The theorem proves U=(I-B A)^(-1)(B v+u). The inverse is ordered, no commutativity is imposed, and no division by the vacuum scalar occurs.

**Definition 1.7 (Ordered joint insertion covariance).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FiniteGaussianSewing.covariance`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/FiniteGaussianSewing.covariance` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The four blocks are (I-BA)^(-1)B, (I-BA)^(-1), (I-AB)^(-1), and (I-AB)^(-1)A. These are ordered matrix products. The lower cross block is the transpose of the upper one under the stated symmetry hypotheses.

**Theorem 1.8 (Symmetric covariance and both true insertion recurrences).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FiniteGaussianSewing.bilinearMoment_wick_recursion`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FiniteGaussianSewing.bilinearMoment_wick_recursion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For symmetric strict contractions A and B, the joint covariance is symmetric. Both insertion-coordinate recurrences have the exact lowering multiplicity alpha_j or beta_j. The matrix identity (I-BA)^(-1)B=B(I-AB)^(-1) is proved by multiplying the two actual ordered inverses. Transposition uses symmetry, with no conjugation or commuting assumption. These are recurrences of the native infinite pairing; no Gaussian moment evaluation is assumed.

**Theorem 1.9 (Finite expansion of the actual external contraction).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FiniteGaussianSewing.row_pair_moments`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FiniteGaussianSewing.row_pair_moments` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The polynomial witnesses are constructed from the actual Gaussian rows. Their absolutely convergent shared-occupation contraction equals the finite double sum of their ordinary monomial coefficients times the actual two-sided insertion moments H(alpha,beta). The proof exchanges each finite sum with the infinite pairing using the previously established norm summability. No effective-kernel identity, moment evaluation or vacuum normalization is assumed in this bridge.

**Theorem 1.10 (Actual pairing equals the normalized native Gaussian moment).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FiniteGaussianSewing.bilinearMoment_native`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FiniteGaussianSewing.bilinearMoment_native` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every pair of shared occupations alpha and beta, H(alpha,beta)=Z times NativeGaussianMoment.nativeMoment(C,alpha.sumElim(beta)), with the ordered symmetric covariance C above and Z=exp((1/2) sum_(k>=0) trace((A B)^(k+1))/(k+1)). Both creation recurrences are used in strong induction on degree(alpha)+degree(beta). Coordinate multiplicities remain alpha_j and beta_j. The zero term is given by the native vacuum_trace_log theorem. No division by Z or nonvanishing hypothesis occurs. The generic nativeMoment_step declaration is reused from NativeGaussianMoment; its proof is not reproduced.

**Definition 1.11 (Effective external kernel with ordered inverses).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FiniteGaussianSewing.effectiveKernel`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/FiniteGaussianSewing.effectiveKernel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For arbitrary finite X,H,Y, symmetric complex P:X by X, Q:Y by Y, A,B:H by H, and arbitrary R:X by H and S:H by Y, set N=(I-B A)^(-1), V=(I-A B)^(-1). The four blocks of E are P+R N B R^T, R N S, S^T V R^T, Q+S^T V A S. Under symmetry and strict shared contractions the lower cross block is the transpose of the upper cross block and E is symmetric. Transpose is bilinear transpose and contains no conjugation.

The external coefficient bridge acts directly on the actual polynomial Gaussian rows. Their internal annihilation equation includes the external lowerings with coefficients R^T and S. With F(d,e) the actual convergent row pairing, U_h the pairing with creation on the first row and V_h that with creation on the second, factorial adjointness gives U=B V+S r and V=A U+R^T l. Here l_j is zero if d_j=0 and otherwise F(d-e_j,e), and r_j is zero if e_j=0 and otherwise F(d,e-e_j). These lowerings carry no extra occupation factor because d and e index ordinary coefficients. Multiplication by the actual ordered inverse solves U=N(B R^T l+S r). The external annihilation equation then has coefficients E_xx and E_xy; the exchanged equation has E_yx and E_yy. The native Gaussian coefficient of E obeys exactly the same two recurrences. Strong induction on external total degree, with base Z, proves the full equality. All finite/infinite sum exchanges use the genuine polynomial-row summability.

**Theorem 1.12 (Full all-occupation finite sewing identity).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FiniteGaussianSewing.finite_sewing`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FiniteGaussianSewing.finite_sewing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all finite complex mode types X,H,Y including empty types, all symmetric P,Q,A,B, all R:X by H and S:H by Y, and all external occupations d,e, assume only norm(toEuclideanCLM(A))<1 and norm(toEuclideanCLM(B))<1. Define K1=[[P,R],[R^T,A]], K2=[[B,S],[S^T,Q]], and E=effectiveKernel(P,Q,A,B,R,S). The theorem proves Summable over n:H→₀N of the norms of weight(n) gaussianCoefficient(K1,d.sumElim(n)) gaussianCoefficient(K2,n.sumElim(e)), and its unconditional sum equals exp((1/2) sum_(k>=0) trace((A B)^(k+1))/(k+1)) times gaussianCoefficient(E,d.sumElim(e)). No full-block or mixed-block bound, commutativity, positivity, nonempty mode premise, occupation cutoff or conclusion certificate is assumed. When H is empty, the contraction is c_P(d)c_Q(e), with Z=1; it need not equal one.

This is a finite coefficient sewing theorem in classical Gaussian/Fock calculus, with no novelty claim. Full corrected fields, arbitrary Gram transport, countable sewing, conformal field theory, fusion, anomalies, string theory and AdS/CFT remain separate obligations.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FiniteGaussianSewing.bilinearMoment`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FiniteGaussianSewing.bilinearMoment_native`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FiniteGaussianSewing.bilinearMoment_resolvent_step`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FiniteGaussianSewing.bilinearMoment_wick_recursion`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FiniteGaussianSewing.covariance`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FiniteGaussianSewing.effectiveKernel`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FiniteGaussianSewing.finite_sewing`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FiniteGaussianSewing.polynomialGaussian`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FiniteGaussianSewing.row`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FiniteGaussianSewing.row_pair_moments`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FiniteGaussianSewing.row_pair_norm_summable`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FiniteGaussianSewing.row_polynomial`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FiniteSqueezedVacuum](FiniteSqueezedVacuum.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/InfiniteGaussianFock](InfiniteGaussianFock.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/NativeGaussianMoment](NativeGaussianMoment.md)

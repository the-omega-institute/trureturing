# Source Jensen Positive Extension

## Abstract

Nonnegative source residues exactly characterize positive real extension.

**Theorem 1.1 (The residue criterion and its arrow matrix).**

$$\begin{aligned}\forall n\in \mathbb{N},\quad \forall \lambda:\operatorname{Fin}(n+1)\to \mathbb{R},\\a_{0}=1\land \operatorname{Injective}(\lambda)\land (\forall i,0< \lambda_{i}\land q_{d-1}(\lambda_{i})=0)\implies\\(\forall i,0< t_{i})\land (\forall i,q_{d}''(t_{i})\neq 0)\\\land (\operatorname{PositiveSplit}(q_{d})\iff (\forall i,0\le \mathrm{eta}_{i}))\\\land ((\forall i,0\le \mathrm{eta}_{i})\implies \operatorname{PosDef}(K)\land \operatorname{charpoly}(K)=q_{d})\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Jensen/SourceJensenPositiveExtension.source_jensen_positive_extension` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let d=n+2, a_k=sourceThetaCoefficient k, and let q_d be the real sourceQ defined by Polynomial.reflect in SourceJensenIntegralExtension. Its complexification is the reflection of the actual sourceJensenPolynomial. All indices i range over Fin(n+1), so there are exactly d-1 nodes. The hypothesis a_0=1 is the source normalization; the frozen source_theta_normalization then supplies strict positivity of every a_k.

$\begin{aligned}d=n+2,\quad t_{i}=\frac{d-1}{d}\lambda_{i},\quad \mathrm{eta}_{i}=\frac{-dq_{d}(t_{i})}{q_{d}''(t_{i})}\\K=\begin{pmatrix}\frac{a_{1}}{d}&{(\sqrt{\mathrm{eta}_{i}})_{i}}^{T}\\(\sqrt{\mathrm{eta}_{i}})_{i}&\operatorname{diag}((t_{i})_{i})\end{pmatrix}\end{aligned}$

K is the concrete matrix arrow n a_1 t eta on Fin(1) + Fin(n+1). Its first diagonal entry is a_1/d, its other diagonal entries are t_i, and its first row and column have entries sqrt(eta_i); all remaining off-diagonal entries are zero. PosDef means strictly positive definite. PositiveSplit(q) means that q splits over the reals and every real zero is strictly positive. The theorem permits eta_i=0 and repeated zeros of q_d.

The previous roots lambda_i are assumed distinct and strictly positive, and satisfy q_(d-1)(lambda_i)=0. The derivative formula proves that t_i are critical nodes; their positive values and nonzero second derivatives are explicit conclusions. No charpoly identity or target positive definiteness is assumed.

The proof binds Mathlib's Schur determinant formula and Lagrange interpolation to this arrow matrix, then uses Hermitian characteristic polynomial factorization and the positive eigenvalue criterion. The converse residue sign uses the upstream split-polynomial logarithmic derivative, differentiation of its finite sum, and nonnegativity of squares. There is no factor induction or additional analytic estimate.

## References

- Truth anchor: `D5/S3/Zeros/Jensen/SourceJensenPositiveExtension.source_jensen_positive_extension`
- Dependency: [D5/S3/Zeros/Jensen/SourceJensenIntegralExtension](SourceJensenIntegralExtension.md)
- Dependency: [D5/S3/Zeros/Jensen/SourceThetaMomentBounds](SourceThetaMomentBounds.md)

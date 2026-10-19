# The spectral geometric Log-Euclidean comparison fails

## Abstract

A positive definite matrix pair refutes Hiai's spectral geometric Log-Euclidean comparison.

Fumio Hiai, Log-majorizations between quasi-geometric type means for matrices, Linear Algebra Appl. 735 (2026), 123–174; arXiv:2510.04691v3. §2, equation (2.3), verbatim: “Fα(A, B) := (A^{−1}#B)^α A(A^{−1}#B)^α.” §2, equation (2.4), verbatim: “SGα,p(A, B) := Fα(A^p, B^p)^{1/p}.” §2, verbatim: “LEα(A, B) := exp((1 − α) log A + α log B)” and “A#αB := A^{1/2}(A^{−1/2}BA^{−1/2})^α A^{1/2}”, with # = #_{1/2}. Problem 3.20, verbatim: “Problem 3.20. The case remaining open is whether SGα,p ≺log LEα for α > 1. Note that this is affirmative if SGα,p ≺log SGα,q if α > 1 and p ≥ q (see Problem 3.12).” The summary table after Problem 3.20 has row “SGα,p ≺log LEα”, with entries “none” for 0 < α < 1 and “?” for α > 1.

**Definition 1.1 (Real matrix powers).**

$$\operatorname{mpow}\left(X, p\right) = \operatorname{cfc}\left(\operatorname{realPowerFunction}\left(p\right), X\right)$$

*Formalization.* `D5/S3/Quantum/Matrix/SpectralPower.mpow` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai (2026). *Log-majorizations between quasi-geometric type means for matrices*. URL: <https://arxiv.org/abs/2510.04691v3>.

*Commentary.*

For a finite complex matrix X and real p, mpow X p is the real continuous functional calculus of t↦t^p at X. On positive definite matrices it is the usual positive real power. The continuous functional calculus is total; the comparison below restricts the inputs to positive definite matrices.

**Definition 1.2 (Weighted geometric means).**

$$\operatorname{wgm}\left(A, B, alpha\right) = \operatorname{mpow}\left(A, \frac{1}{2}\right) \cdot \operatorname{mpow}\left(\operatorname{mpow}\left(A, \frac{0 - 1}{2}\right) \cdot B \cdot \operatorname{mpow}\left(A, \frac{0 - 1}{2}\right), alpha\right) \cdot \operatorname{mpow}\left(A, \frac{1}{2}\right)$$

*Formalization.* `D5/S3/Quantum/Matrix/SpectralGeometricLogEuclideanRefutation.wgm` (`✓ std3`).

*Citation.* Fumio Hiai (2026). *Log-majorizations between quasi-geometric type means for matrices*. URL: <https://arxiv.org/abs/2510.04691v3>.

*Commentary.*

The formula is A^(1/2)(A^(−1/2)BA^(−1/2))^αA^(1/2), with every power interpreted by mpow. At α=1/2 this is the geometric mean A#B.

**Definition 1.3 (Weighted spectral geometric means).**

$$\operatorname{specMean}\left(A, B, alpha\right) = \operatorname{mpow}\left(\operatorname{wgm}\left(\operatorname{inverse}\left(A\right), B, \frac{1}{2}\right), alpha\right) \cdot A \cdot \operatorname{mpow}\left(\operatorname{wgm}\left(\operatorname{inverse}\left(A\right), B, \frac{1}{2}\right), alpha\right)$$

*Formalization.* `D5/S3/Quantum/Matrix/SpectralGeometricLogEuclideanRefutation.specMean` (`✓ std3`).

*Citation.* Fumio Hiai (2026). *Log-majorizations between quasi-geometric type means for matrices*. URL: <https://arxiv.org/abs/2510.04691v3>.

*Commentary.*

Equation (2.3) defines Fα(A,B)=(A^(−1)#B)^α A (A^(−1)#B)^α. The inverse is the genuine matrix inverse for the positive definite inputs.

**Definition 1.4 (The power parameter).**

$$\operatorname{SG}\left(alpha, p, A, B\right) = \operatorname{mpow}\left(\operatorname{specMean}\left(\operatorname{mpow}\left(A, p\right), \operatorname{mpow}\left(B, p\right), alpha\right), \frac{1}{p}\right)$$

*Formalization.* `D5/S3/Quantum/Matrix/SpectralGeometricLogEuclideanRefutation.SG` (`✓ std3`).

*Citation.* Fumio Hiai (2026). *Log-majorizations between quasi-geometric type means for matrices*. URL: <https://arxiv.org/abs/2510.04691v3>.

*Commentary.*

Equation (2.4) applies Fα to A^p and B^p and then takes the 1/p power. The claim uses only p>0.

**Definition 1.5 (Log-Euclidean means).**

$$\operatorname{LE}\left(alpha, A, B\right) = \operatorname{cfc}\left(exp, \operatorname{smul}\left(1 - alpha, \operatorname{cfc}\left(log, A\right)\right) + \operatorname{smul}\left(alpha, \operatorname{cfc}\left(log, B\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Matrix/SpectralPower.LE` (`✓ std3`).

*Citation.* Fumio Hiai (2026). *Log-majorizations between quasi-geometric type means for matrices*. URL: <https://arxiv.org/abs/2510.04691v3>.

*Commentary.*

The real logarithm and exponential are applied through the continuous functional calculus. The logarithmic generator is (1−α)log A+α log B.

**Definition 1.6 (Log-majorization).**

$$\forall m: \mathbb{N}, \forall X: \operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), \mathbb{C}\right), \forall Y: \operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), \mathbb{C}\right), \forall hX: \operatorname{IsHermitian}\left(X\right), \forall hY: \operatorname{IsHermitian}\left(Y\right), \operatorname{LogMajorized}\left(X, Y, hX, hY\right) \Leftrightarrow ((\forall s: \operatorname{Finset}\left(\operatorname{Fin}\left(m\right)\right), \exists t: \operatorname{Finset}\left(\operatorname{Fin}\left(m\right)\right), (\operatorname{card}\left(t\right) = \operatorname{card}\left(s\right)) \land (\operatorname{eigenvalueProduct}\left(hX, s\right) \le \operatorname{eigenvalueProduct}\left(hY, t\right))) \land (\operatorname{det}\left(X\right) = \operatorname{det}\left(Y\right)))$$

*Formalization.* `D5/S3/Quantum/Matrix/SpectralGeometricLogEuclideanRefutation.LogMajorized` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai (2026). *Log-majorizations between quasi-geometric type means for matrices*. URL: <https://arxiv.org/abs/2510.04691v3>.

*Commentary.*

For Hermitian X,Y of size m, LogMajorized requires that for every finite index set s there is an index set t of the same cardinality with the product of X's eigenvalues indexed by s at most the product of Y's eigenvalues indexed by t. It also requires det X=det Y. The formula's eigenvalueProduct means this finite product, using the indicated Hermitian proof hX or hY. For positive definite matrices this is equivalent to the usual comparison of the products of the k largest eigenvalues for each k.

**Definition 1.7 (The open case of Problem 3.20).**

$$claim \Leftrightarrow (\forall alpha: \mathbb{R}, \forall p: \mathbb{R}, \forall m: \mathbb{N}, \forall A: \operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), \mathbb{C}\right), \forall B: \operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), \mathbb{C}\right), (1 < alpha) \Rightarrow ((0 < p) \Rightarrow ((\operatorname{PosDef}\left(A\right)) \Rightarrow ((\operatorname{PosDef}\left(B\right)) \Rightarrow (\forall hX: \operatorname{IsHermitian}\left(\operatorname{SG}\left(alpha, p, A, B\right)\right), \forall hY: \operatorname{IsHermitian}\left(\operatorname{LE}\left(alpha, A, B\right)\right), \operatorname{LogMajorized}\left(\operatorname{SG}\left(alpha, p, A, B\right), \operatorname{LE}\left(alpha, A, B\right), hX, hY\right))))))$$

*Formalization.* `D5/S3/Quantum/Matrix/SpectralGeometricLogEuclideanRefutation.claim` (`✓ std3`).

*Citation.* Fumio Hiai (2026). *Log-majorizations between quasi-geometric type means for matrices*. URL: <https://arxiv.org/abs/2510.04691v3>.

*Commentary.*

The assertion quantifies over all real α>1 and p>0, dimensions m, and positive definite complex matrices A,B of size m. For each Hermitian proof of each mean, it requires the stated log-majorization. Both means are Hermitian on these inputs. The general source assertion includes m=2, so a violation in that dimension refutes the open case.

**Theorem 1.8 (An exact two-dimensional counterexample).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/SpectralGeometricLogEuclideanRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/hiai-2026-spectral-geometric-log-euclidean-refutation` (refuted) by `D5/S3/Quantum/Matrix/SpectralGeometricLogEuclideanRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hiai-2026-spectral-geometric-log-euclidean-refutation","declaration_gid":"D5/S3/Quantum/Matrix/SpectralGeometricLogEuclideanRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai (2026). *Log-majorizations between quasi-geometric type means for matrices*. URL: <https://arxiv.org/abs/2510.04691v3>.

*Commentary.*

Take α=2, p=1, A=diag(1,1048576), and B=[[272,504],[504,1853]]/125. The orthogonal matrix U=[[24,7],[−7,24]]/25 gives B=U diag(1,16) U*, proving positivity. Put X=A^(1/2)BA^(1/2), T=77761424/5, K=X+4096I, and H=B+4096A^(−1). The exact identity K²=TX and positivity identify X^(1/2)=K/√T. Thus L=A^(−1)#B=H/√T, and the identity LAL=B yields SG₂,₁=L²AL²=LBL=HBH/T. Its entry of index (0,0) is 286558676/121502225>2. On the other side, −log A+2log B=(log 2)N, where N=[[392,1344],[1344,−7892]]/625. The factorization I−N=V diag(233/625,285/233) V*, with V=[[1,0],[−1344/233,1]], proves N≤I. The spectral bound and scalar exponential monotonicity imply LE₂≤2I, so all its eigenvalues are at most 2. If all SG eigenvalues were at most 2, spectral calculus would give SG≤2I, contradicting its diagonal entry. Taking the singleton consisting of an SG eigenvalue above 2 contradicts log-majorization. Determinant equality is unnecessary. The companion problem gives the positive-power reduction and an asymptotic family for every α>1 as mathematical reasoning, not additional Lean theorems. The sufficient decreasing-power route in Problem 3.20 cannot hold universally when combined with the paper's small-power limit to LE; the remaining companion questions of Problem 3.12 remain open here.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/SpectralGeometricLogEuclideanRefutation.LogMajorized`
- Truth anchor: `D5/S3/Quantum/Matrix/SpectralGeometricLogEuclideanRefutation.SG`
- Truth anchor: `D5/S3/Quantum/Matrix/SpectralGeometricLogEuclideanRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Matrix/SpectralGeometricLogEuclideanRefutation.result`
- Truth anchor: `D5/S3/Quantum/Matrix/SpectralGeometricLogEuclideanRefutation.specMean`
- Truth anchor: `D5/S3/Quantum/Matrix/SpectralGeometricLogEuclideanRefutation.wgm`
- Truth anchor: `D5/S3/Quantum/Matrix/SpectralPower.LE`
- Truth anchor: `D5/S3/Quantum/Matrix/SpectralPower.mpow`
- Dependency: [D5/S3/Quantum/Matrix/SpectralPower](SpectralPower.md)

# Lin's operator Wielandt norm conjecture fails

## Abstract

A unital 2-positive complex-linear map violates Lin's operator Wielandt product norm bound.

Minghua Lin, On an operator Kantorovich inequality for positive linear maps, J. Math. Anal. Appl. 402 (2013), 127–132; arXiv:1212.5690v1, §3, p. 6, verbatim: “Theorem 3.1. [3] Let 0 < m ≤ A ≤ M and let X, Y be two partial isometries on H whose final spaces are orthogonal to each other. Then for every 2-positive linear map Φ, Φ(X*AY)Φ(Y*AY)⁻¹Φ(Y*AX) ≤ ((M−m)/(M+m))² Φ(X*AX).” §3, pp. 6–7, immediately before Conjecture 3.4, verbatim: “Despite the invalidity of (3.6), there is some evidence that the following assertion could be true. We have been unable to prove (or disprove) it.” §3, p. 7, verbatim: “Conjecture 3.4. Under the same condition as in Theorem 3.1. Then for every 2-positive linear map Φ, ‖Φ(X*AY)Φ(Y*AY)⁻¹Φ(Y*AX)Φ(X*AX)⁻¹‖ ≤ ((M−m)/(M+m))².” §3, p. 6, verbatim: “Let Φ be a unital positive linear map between C*-algebras. We say that Φ is 2-positive if whenever the 2 × 2 operator matrix [[A, B],[B*, C]] is positive, then so is [[Φ(A), Φ(B)],[Φ(B*), Φ(C)]].” P. Zhang, Remarks on an operator Wielandt inequality, arXiv:1506.00737, describes the conjecture as still open.

**Definition 1.1 (Partial isometries).**

$$\forall n: \mathbb{N}, \forall X: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), \operatorname{IsPartialIsometry}\left(X\right) \Leftrightarrow (X \cdot \operatorname{adjoint}\left(X\right) \cdot X = X)$$

*Formalization.* `D5/S3/Quantum/Matrix/OperatorWielandtNormRefutation.IsPartialIsometry` (`✓ std3`).

*Citation.* Minghua Lin (2013). *On an operator Kantorovich inequality for positive linear maps*. DOI: [10.1016/j.jmaa.2013.01.015](https://doi.org/10.1016/j.jmaa.2013.01.015). URL: <https://arxiv.org/abs/1212.5690v1>.

*Commentary.*

For a complex n×n matrix X, the condition is XX*X=X. Orthogonality of the final spaces is expressed separately by X*Y=0: its entries are inner products between columns of X and Y, so the two ranges are orthogonal.

**Definition 1.2 (Unital 2-positive linear maps).**

$$\forall n: \mathbb{N}, \forall k: \mathbb{N}, \forall Phi: \operatorname{ComplexLinearMap}\left(\operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), \operatorname{Matrix}\left(\operatorname{Fin}\left(k\right), \operatorname{Fin}\left(k\right), \mathbb{C}\right)\right), \operatorname{IsUnitalTwoPositive}\left(Phi\right) \Leftrightarrow ((\operatorname{Phi}\left(I\right) = I) \land (\forall A: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), \forall B: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), \forall C: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), (\operatorname{PosSemidef}\left(\operatorname{fromBlocks}\left(A, B, \operatorname{adjoint}\left(B\right), C\right)\right)) \Rightarrow (\operatorname{PosSemidef}\left(\operatorname{fromBlocks}\left(\operatorname{Phi}\left(A\right), \operatorname{Phi}\left(B\right), \operatorname{Phi}\left(\operatorname{adjoint}\left(B\right)\right), \operatorname{Phi}\left(C\right)\right)\right))))$$

*Formalization.* `D5/S3/Quantum/Matrix/OperatorWielandtNormRefutation.IsUnitalTwoPositive` (`✓ std3`).

*Citation.* Minghua Lin (2013). *On an operator Kantorovich inequality for positive linear maps*. DOI: [10.1016/j.jmaa.2013.01.015](https://doi.org/10.1016/j.jmaa.2013.01.015). URL: <https://arxiv.org/abs/1212.5690v1>.

*Commentary.*

The map is complex-linear, sends I to I, and preserves positive semidefiniteness of every 2×2 block matrix [[A,B],[B*,C]] by entrywise application. This implies positivity by taking B=C=0 and restricting the positive image to its first block. Thus the predicate encodes the unital positive maps in the source definition.

**Definition 1.3 (Euclidean operator norm bound).**

$$\forall k: \mathbb{N}, \forall T: \operatorname{Matrix}\left(\operatorname{Fin}\left(k\right), \operatorname{Fin}\left(k\right), \mathbb{C}\right), \forall c: \mathbb{R}, \operatorname{NormLE}\left(T, c\right) \Leftrightarrow (\forall v: \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Fin}\left(k\right)\right), \operatorname{norm}\left(\operatorname{apply}\left(T, v\right)\right) \le c \cdot \operatorname{norm}\left(v\right))$$

*Formalization.* `D5/S3/Quantum/Matrix/OperatorWielandtNormRefutation.NormLE` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Minghua Lin (2013). *On an operator Kantorovich inequality for positive linear maps*. DOI: [10.1016/j.jmaa.2013.01.015](https://doi.org/10.1016/j.jmaa.2013.01.015). URL: <https://arxiv.org/abs/1212.5690v1>.

*Commentary.*

NormLE T c means that every vector v in the complex Euclidean space satisfies ‖Tv‖≤c‖v‖. Matrix.toEuclideanLin supplies precisely this linear action, so this is the induced operator norm inequality.

**Definition 1.4 (Conjecture 3.4 in finite dimensions).**

$$claim \Leftrightarrow (\forall n: \mathbb{N}, \forall k: \mathbb{N}, \forall A: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), \forall X: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), \forall Y: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), \forall m: \mathbb{R}, \forall M: \mathbb{R}, \forall Phi: \operatorname{ComplexLinearMap}\left(\operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), \operatorname{Matrix}\left(\operatorname{Fin}\left(k\right), \operatorname{Fin}\left(k\right), \mathbb{C}\right)\right), (0 < m) \Rightarrow ((m \le M) \Rightarrow ((\operatorname{IsHermitian}\left(A\right)) \Rightarrow ((\operatorname{PosSemidef}\left(A - m \cdot I\right)) \Rightarrow ((\operatorname{PosSemidef}\left(M \cdot I - A\right)) \Rightarrow ((\operatorname{IsPartialIsometry}\left(X\right)) \Rightarrow ((\operatorname{IsPartialIsometry}\left(Y\right)) \Rightarrow ((\operatorname{adjoint}\left(X\right) \cdot Y = 0) \Rightarrow ((\operatorname{IsUnitalTwoPositive}\left(Phi\right)) \Rightarrow ((\operatorname{IsUnit}\left(\operatorname{det}\left(\operatorname{Phi}\left(\operatorname{adjoint}\left(Y\right) \cdot A \cdot Y\right)\right)\right)) \Rightarrow ((\operatorname{IsUnit}\left(\operatorname{det}\left(\operatorname{Phi}\left(\operatorname{adjoint}\left(X\right) \cdot A \cdot X\right)\right)\right)) \Rightarrow (\operatorname{NormLE}\left(\operatorname{Phi}\left(\operatorname{adjoint}\left(X\right) \cdot A \cdot Y\right) \cdot \operatorname{inverse}\left(\operatorname{Phi}\left(\operatorname{adjoint}\left(Y\right) \cdot A \cdot Y\right)\right) \cdot \operatorname{Phi}\left(\operatorname{adjoint}\left(Y\right) \cdot A \cdot X\right) \cdot \operatorname{inverse}\left(\operatorname{Phi}\left(\operatorname{adjoint}\left(X\right) \cdot A \cdot X\right)\right), (\frac{M - m}{M + m})^{2}\right)))))))))))))$$

*Formalization.* `D5/S3/Quantum/Matrix/OperatorWielandtNormRefutation.claim` (`✓ std3`).

*Citation.* Minghua Lin (2013). *On an operator Kantorovich inequality for positive linear maps*. DOI: [10.1016/j.jmaa.2013.01.015](https://doi.org/10.1016/j.jmaa.2013.01.015). URL: <https://arxiv.org/abs/1212.5690v1>.

*Commentary.*

The assertion quantifies over all finite dimensions n,k, complex matrices A,X,Y, real bounds m,M, and complex-linear maps Φ. It assumes 0<m≤M, A Hermitian, mI≤A≤MI, partial isometries X,Y with orthogonal ranges, and a unital 2-positive Φ. Both compressed images must have unit determinants, so their inverses are genuine. The general source assertion includes this finite-dimensional case; failure here refutes Conjecture 3.4.

**Theorem 1.5 (An exact four-dimensional counterexample).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/OperatorWielandtNormRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/lin-2013-operator-wielandt-norm-refutation` (refuted) by `D5/S3/Quantum/Matrix/OperatorWielandtNormRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"lin-2013-operator-wielandt-norm-refutation","declaration_gid":"D5/S3/Quantum/Matrix/OperatorWielandtNormRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Minghua Lin (2013). *On an operator Kantorovich inequality for positive linear maps*. DOI: [10.1016/j.jmaa.2013.01.015](https://doi.org/10.1016/j.jmaa.2013.01.015). URL: <https://arxiv.org/abs/1212.5690v1>.

*Commentary.*

Take n=k=4, m=1/25, M=13, A=[[9,0,2,0],[0,2,1,0],[2,1,1,0],[0,0,0,1]], P=X=diag(1,1,0,0), and Y with entries Y(2,0)=Y(3,1)=1 and all others zero, using zero-based indices. Define Φ(Z)=PZP*+YZY*. Exact LDL* certificates have diagonals (224/25,49/25,33/9800,24/25) for A−mI and (4,11,120/11,12) for MI−A. The lower factor has third row (25/112,25/49,1,0), and the upper factor has third row (−1/2,−1/11,1,0); their other rows equal those of I. Positive diagonal congruences certify the bounds. The proof checks XX*X=X, YY*Y=Y, and X*Y=0. For a positive block M, conjugation by diag(P,P) and diag(Y,Y) gives positive summands whose sum is its entrywise Φ-image. PP*+YY*=I gives unitality. The images Φ(Y*AY)=I and Φ(X*AX)=diag(9,2,9,2) have determinants 1 and 324. Their inverses are I and diag(1/9,1/2,1/9,1/2). The product T consists of two copies of G=[[4/9,1],[2/9,1/2]]. For the unit coordinate vector of index 1, ‖Te₂‖²=5/4>(26244/26569)², whereas the conjectured constant is 26244/26569. The hypotheses therefore hold and the norm conclusion fails. The order inequality survives: D^(−1/2)CE^(−1)C*D^(−1/2) is bounded above by qI, but CE^(−1)C*D^(−1) is a non-normal similarity of it. This mechanism and the unbounded parameter family in the companion problem are exact mathematical reasoning, not further Lean theorems. Conditional results assuming Conjecture 3.4 retain their conditional form and cannot apply that conjecture universally.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/OperatorWielandtNormRefutation.IsPartialIsometry`
- Truth anchor: `D5/S3/Quantum/Matrix/OperatorWielandtNormRefutation.IsUnitalTwoPositive`
- Truth anchor: `D5/S3/Quantum/Matrix/OperatorWielandtNormRefutation.NormLE`
- Truth anchor: `D5/S3/Quantum/Matrix/OperatorWielandtNormRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Matrix/OperatorWielandtNormRefutation.result`

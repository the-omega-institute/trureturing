# Arbitrary even-order convexity of split covariance intersection

## Abstract

The split covariance intersection covariance has nonnegative derivatives of every positive even order for both its log determinant and its trace, with semidefinite input covariances and positive definite pair sums.

**Definition 1.1 (The split covariance intersection covariance).**

$$\forall n \in \mathbb{N},\; \forall A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{R}\right),\; \forall B \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{R}\right),\; \forall C \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{R}\right),\; \forall D \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{R}\right),\; \forall w \in \mathbb{R},\; \operatorname{splitP}\left(A, B, C, D, w\right) = \operatorname{inv}\left(\operatorname{inv}\left(\operatorname{smul}\left(\operatorname{inv}\left(w\right), A\right) + B\right) + \operatorname{inv}\left(\operatorname{smul}\left(\operatorname{inv}\left(1 - w\right), C\right) + D\right)\right)$$

*Formalization.* `D5/S3/Estimation/SplitCovarianceIntersectionEvenConvexity.splitP` (`✓ std3`).

*Citation.* Hao Li (2026). *Conjecture About Arbitrary Even-Order Convexity of w-Optimization of the Split CIF*. URL: <https://arxiv.org/abs/2606.27260v1>.

*Commentary.*

Section 2.1, p. 2: "Matrices mentioned in this paper are symmetric matrices by default. Given matrices $\mathbf{P}_{1d}$, $\mathbf{P}_{1i}$, $\mathbf{P}_{2d}$, and $\mathbf{P}_{2i}$ that are positive semi-definite, i.e., $\mathbf{P}_{1d} \ge \mathbf{0}$, $\mathbf{P}_{1i} \ge \mathbf{0}$, $\mathbf{P}_{2d} \ge \mathbf{0}$, $\mathbf{P}_{2i} \ge \mathbf{0}$. Besides, the matrices $\mathbf{P}_{1d} + \mathbf{P}_{1i}$ and $\mathbf{P}_{2d} + \mathbf{P}_{2i}$ which normally correspond to covariances of certain estimates are always positive definite, i.e., $\mathbf{P}_{1d} + \mathbf{P}_{1i} > 0$ and $\mathbf{P}_{2d} + \mathbf{P}_{2i} > 0$. For $w \in [0,1]$, define"; equation (1) reads $\mathbf{P}_{1}(w) = \mathbf{P}_{1d}/w + \mathbf{P}_{1i}$, $\mathbf{P}_{2}(w) = \mathbf{P}_{2d}/(1 - w) + \mathbf{P}_{2i}$, $\mathbf{P}(w) = (\mathbf{P}_{1}(w)^{-1} + \mathbf{P}_{2}(w)^{-1})^{-1}$. "When $w = 0$ or $w = 1$, $\mathbf{P}(w)$ denotes the limit value as $w \to 0$ or $w \to 1$ respectively." The encoding uses real matrices indexed by Fin n and A, B, C, D for the four source matrices in that order. Scalar division by w is multiplication by the reciprocal scalar, denoted smul in the formula; inv is the matrix inverse. The definition is total in Lean. The theorem concerns only 0 < w < 1; the endpoints w in {0,1} and their limit convention are not part of the formal statement.

**Definition 1.2 (Li's arbitrary even-order convexity conjecture).**

$$claim \Leftrightarrow (\forall n \in \mathbb{N},\; \forall A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{R}\right),\; \forall B \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{R}\right),\; \forall C \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{R}\right),\; \forall D \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{R}\right),\; (\operatorname{PosSemidef}\left(A\right)) \Rightarrow ((\operatorname{PosSemidef}\left(B\right)) \Rightarrow ((\operatorname{PosSemidef}\left(C\right)) \Rightarrow ((\operatorname{PosSemidef}\left(D\right)) \Rightarrow ((\operatorname{PosDef}\left(A + B\right)) \Rightarrow ((\operatorname{PosDef}\left(C + D\right)) \Rightarrow (\forall k \in \mathbb{N},\; (1 \le k) \Rightarrow (\forall w \in \mathbb{R},\; (w \in \operatorname{Ioo}\left(0, 1\right)) \Rightarrow ((0 \le \operatorname{iteratedDeriv}\left(2 \cdot k, (x \mapsto \operatorname{log}\left(\operatorname{det}\left(\operatorname{splitP}\left(A, B, C, D, x\right)\right)\right)), w\right)) \land (0 \le \operatorname{iteratedDeriv}\left(2 \cdot k, (x \mapsto \operatorname{trace}\left(\operatorname{splitP}\left(A, B, C, D, x\right)\right)), w\right)))))))))))$$

*Formalization.* `D5/S3/Estimation/SplitCovarianceIntersectionEvenConvexity.claim` (`✓ std3`).

*Citation.* Hao Li (2026). *Conjecture About Arbitrary Even-Order Convexity of w-Optimization of the Split CIF*. URL: <https://arxiv.org/abs/2606.27260v1>.

*Commentary.*

Section 2.2, p. 3: "For a generic function $f(x)$, if its $m$-th-order derivative is always non-negative (or positive semi-definite), namely $\frac{d^{m}}{dx^{m}} f(x) \ge 0$, then it is said to have the **$m$-th-order convexity** [16]." "The proposed conjecture is that **the $w$-optimization problem has arbitrary even-order convexity**, more specifically, for $k \in \{1, 2, 3, \cdot\cdot\cdot\}$ we always have" $\frac{d^{2 k}}{dw^{2 k}} \operatorname{ln} \operatorname{det}(\mathbf{P}(w)) \ge 0$, $\frac{d^{2 k}}{dw^{2 k}} tr \{ \mathbf{P}(w) \} \ge 0$ (7a), (7b). The encoding quantifies over every natural dimension n, including the harmless empty dimension, all four positive semidefinite real matrices with A+B and C+D positive definite, all natural k at least 1, and all real w in (0,1). PosSemidef includes symmetry for real matrices. The iteratedDeriv operator is the ordinary iterated real derivative; log is Real.log. Neither individual positive definiteness nor commutativity is assumed.

**Theorem 1.3 (Both even-order derivative inequalities).**

$$\forall n \in \mathbb{N},\; \forall A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{R}\right),\; \forall B \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{R}\right),\; \forall C \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{R}\right),\; \forall D \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{R}\right),\; (\operatorname{PosSemidef}\left(A\right)) \Rightarrow ((\operatorname{PosSemidef}\left(B\right)) \Rightarrow ((\operatorname{PosSemidef}\left(C\right)) \Rightarrow ((\operatorname{PosSemidef}\left(D\right)) \Rightarrow ((\operatorname{PosDef}\left(A + B\right)) \Rightarrow ((\operatorname{PosDef}\left(C + D\right)) \Rightarrow (\forall k \in \mathbb{N},\; (1 \le k) \Rightarrow (\forall w \in \mathbb{R},\; (w \in \operatorname{Ioo}\left(0, 1\right)) \Rightarrow ((0 \le \operatorname{iteratedDeriv}\left(2 \cdot k, (x \mapsto \operatorname{log}\left(\operatorname{det}\left(\operatorname{splitP}\left(A, B, C, D, x\right)\right)\right)), w\right)) \land (0 \le \operatorname{iteratedDeriv}\left(2 \cdot k, (x \mapsto \operatorname{trace}\left(\operatorname{splitP}\left(A, B, C, D, x\right)\right)), w\right))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/SplitCovarianceIntersectionEvenConvexity.result` (`✓ std3`). ∎

*Resolves.* `Problems/li-2026-split-cif-even-order-convexity` (proved) by `D5/S3/Estimation/SplitCovarianceIntersectionEvenConvexity.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"li-2026-split-cif-even-order-convexity","declaration_gid":"D5/S3/Estimation/SplitCovarianceIntersectionEvenConvexity.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Hao Li (2026). *Conjecture About Arbitrary Even-Order Convexity of w-Optimization of the Split CIF*. URL: <https://arxiv.org/abs/2606.27260v1>.

*Commentary.*

For positive definite inputs, introduce a three-block positive definite affine pencil M and its lower two-block compression K. The upper inverse corner is splitP, and det(splitP) = det(K)/det(M). Noncommutative differentiation of the affine inverse gives positive semidefinite even inverse derivatives by a matrix congruence. Spectral diagonalization and scalar Jensen applied to squared overlaps give the even-power trace inequality for isometric compression; this makes each even derivative of log det(K) minus log det(M) nonnegative. Adding a positive scalar multiple of the identity to each input and taking the scalar to zero extends both inequalities to semidefinite inputs. Joint smoothness near each interior weight gives continuity of every fixed-order derivative in the regularization parameter.

## References

- Truth anchor: `D5/S3/Estimation/SplitCovarianceIntersectionEvenConvexity.claim`
- Truth anchor: `D5/S3/Estimation/SplitCovarianceIntersectionEvenConvexity.result`
- Truth anchor: `D5/S3/Estimation/SplitCovarianceIntersectionEvenConvexity.splitP`

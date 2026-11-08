# Zimmermann--Stoye Conjecture 1

## Abstract

Sharp codimension-one Euclidean Stiefel curvature bounds and endpoints.

**Definition 1.1 (The Stiefel set).**

$$\forall n \in \operatorname {Nat},\; \forall p \in \operatorname {Nat},\; \operatorname {stiefel}\left(n, p\right) = \operatorname {setOf}\left(\operatorname {fun} (U: \operatorname {Matrix}\left(\operatorname {Fin}\left(n\right), \operatorname {Fin}\left(p\right), \operatorname {Real}\right)) \mapsto \operatorname {Matrix.transpose}\left(U\right) \cdot U = 1\right)$$

*Formalization.* `D5/S3/Geometry/Riemannian/ZimmermannStoyeCodimensionOneCurvature.stiefel` (`✓ std3`).

*Citation.* Ralf Zimmermann and Jakob Stoye (2024). *High curvature means low-rank: On the sectional curvature of Grassmann and Stiefel manifolds and the underlying matrix trace inequalities*. DOI: [10.1137/24M1655755](https://doi.org/10.1137/24M1655755). URL: <https://arxiv.org/abs/2403.01879v3>.

*Commentary.*

The Stiefel manifold is St(n,p) = {U ∈ ℝⁿˣᵖ | UᵀU = Iₚ}. (Notational specifics, PDF page 2.) The matrix equation uses real matrices and the identity matrix of size p.

**Definition 1.2 (Orthonormal tangent blocks).**

$$\forall p \in \operatorname {Nat},\; \forall q \in \operatorname {Nat},\; \forall A1 \in \operatorname {Matrix}\left(\operatorname {Fin}\left(p\right), \operatorname {Fin}\left(p\right), \operatorname {Real}\right),\; \forall A2 \in \operatorname {Matrix}\left(\operatorname {Fin}\left(p\right), \operatorname {Fin}\left(p\right), \operatorname {Real}\right),\; \forall B1 \in \operatorname {Matrix}\left(\operatorname {Fin}\left(q\right), \operatorname {Fin}\left(p\right), \operatorname {Real}\right),\; \forall B2 \in \operatorname {Matrix}\left(\operatorname {Fin}\left(q\right), \operatorname {Fin}\left(p\right), \operatorname {Real}\right),\; \operatorname {orthonormalTangentBlocks}\left(A1, A2, B1, B2\right) = \left((\operatorname {Matrix.transpose}\left(A1\right) = -A1) \land ((\operatorname {Matrix.transpose}\left(A2\right) = -A2) \land ((\left\lVert A1 \right\rVert^{2} + \left\lVert B1 \right\rVert^{2} = 1) \land ((\left\lVert A2 \right\rVert^{2} + \left\lVert B2 \right\rVert^{2} = 1) \land (\operatorname {Matrix.trace}\left(\operatorname {Matrix.transpose}\left(A1\right) \cdot A2\right) + \operatorname {Matrix.trace}\left(\operatorname {Matrix.transpose}\left(B1\right) \cdot B2\right) = 0))))\right)$$

*Formalization.* `D5/S3/Geometry/Riemannian/ZimmermannStoyeCodimensionOneCurvature.orthonormalTangentBlocks` (`✓ std3`).

*Citation.* Ralf Zimmermann and Jakob Stoye (2024). *High curvature means low-rank: On the sectional curvature of Grassmann and Stiefel manifolds and the underlying matrix trace inequalities*. DOI: [10.1137/24M1655755](https://doi.org/10.1137/24M1655755). URL: <https://arxiv.org/abs/2403.01879v3>.

*Commentary.*

The source states: “The matrices X,Y form a (Riemannian) ONB if and only if 1 = ‖Aᵢ‖²_F + ‖Bᵢ‖²_F, i=1,2, 0 = tr(A₁ᵀA₂) + tr(B₁ᵀB₂).” (Section 3.3, PDF page 15.) Its tangent representation has Aᵢᵀ = −Aᵢ. The five equations express these two skew conditions and the three orthonormality equations, with real p by p top blocks and real q by p bottom blocks.

**Definition 1.3 (The Euclidean curvature expression).**

$$\forall p \in \operatorname {Nat},\; \forall q \in \operatorname {Nat},\; \forall A1 \in \operatorname {Matrix}\left(\operatorname {Fin}\left(p\right), \operatorname {Fin}\left(p\right), \operatorname {Real}\right),\; \forall A2 \in \operatorname {Matrix}\left(\operatorname {Fin}\left(p\right), \operatorname {Fin}\left(p\right), \operatorname {Real}\right),\; \forall B1 \in \operatorname {Matrix}\left(\operatorname {Fin}\left(q\right), \operatorname {Fin}\left(p\right), \operatorname {Real}\right),\; \forall B2 \in \operatorname {Matrix}\left(\operatorname {Fin}\left(q\right), \operatorname {Fin}\left(p\right), \operatorname {Real}\right),\; \operatorname {euclideanSectionalCurvature}\left(A1, A2, B1, B2\right) = \left\lVert B1 \cdot A2 - B2 \cdot A1 \right\rVert^{2} + \frac{1}{2} \cdot \left\lVert B1 \cdot \operatorname {Matrix.transpose}\left(B2\right) - B2 \cdot \operatorname {Matrix.transpose}\left(B1\right) \right\rVert^{2} - \frac{1}{2} \cdot \left\lVert \operatorname {Matrix.transpose}\left(B1\right) \cdot B2 - \operatorname {Matrix.transpose}\left(B2\right) \cdot B1 \right\rVert^{2} + \frac{1}{4} \cdot \left\lVert A1 \cdot A2 - A2 \cdot A1 - \left(\operatorname {Matrix.transpose}\left(B2\right) \cdot B1 - \operatorname {Matrix.transpose}\left(B1\right) \cdot B2\right) \right\rVert^{2}$$

*Formalization.* `D5/S3/Geometry/Riemannian/ZimmermannStoyeCodimensionOneCurvature.euclideanSectionalCurvature` (`✓ std3`).

*Citation.* Ralf Zimmermann and Jakob Stoye (2024). *High curvature means low-rank: On the sectional curvature of Grassmann and Stiefel manifolds and the underlying matrix trace inequalities*. DOI: [10.1137/24M1655755](https://doi.org/10.1137/24M1655755). URL: <https://arxiv.org/abs/2403.01879v3>.

*Commentary.*

Equation (26) gives the Euclidean sectional curvature on an orthonormal tangent pair. Matrix norms are Frobenius norms, and the commutator is A₁A₂−A₂A₁. The orthogonal base-point isometry identifies every tangent plane with these blocks; this identification is the source's geometric interpretation of the matrix expression.

**Definition 1.4 (The conjectured sharp interval).**

$$\operatorname {claim} = \left(\forall n \in \operatorname {Nat},\; (4 \le n) \Rightarrow ((\forall A1 \in \operatorname {Matrix}\left(\operatorname {Fin}\left(n - 1\right), \operatorname {Fin}\left(n - 1\right), \operatorname {Real}\right),\; \forall A2 \in \operatorname {Matrix}\left(\operatorname {Fin}\left(n - 1\right), \operatorname {Fin}\left(n - 1\right), \operatorname {Real}\right),\; \forall B1 \in \operatorname {Matrix}\left(\operatorname {Fin}\left(1\right), \operatorname {Fin}\left(n - 1\right), \operatorname {Real}\right),\; \forall B2 \in \operatorname {Matrix}\left(\operatorname {Fin}\left(1\right), \operatorname {Fin}\left(n - 1\right), \operatorname {Real}\right),\; (\operatorname {orthonormalTangentBlocks}\left(A1, A2, B1, B2\right)) \Rightarrow ((-\frac{1}{2} \le \operatorname {euclideanSectionalCurvature}\left(A1, A2, B1, B2\right)) \land (\operatorname {euclideanSectionalCurvature}\left(A1, A2, B1, B2\right) \le \frac{1}{2}))) \land ((\exists A1 \in \operatorname {Matrix}\left(\operatorname {Fin}\left(n - 1\right), \operatorname {Fin}\left(n - 1\right), \operatorname {Real}\right),\; \exists A2 \in \operatorname {Matrix}\left(\operatorname {Fin}\left(n - 1\right), \operatorname {Fin}\left(n - 1\right), \operatorname {Real}\right),\; \exists B1 \in \operatorname {Matrix}\left(\operatorname {Fin}\left(1\right), \operatorname {Fin}\left(n - 1\right), \operatorname {Real}\right),\; \exists B2 \in \operatorname {Matrix}\left(\operatorname {Fin}\left(1\right), \operatorname {Fin}\left(n - 1\right), \operatorname {Real}\right),\; (\operatorname {orthonormalTangentBlocks}\left(A1, A2, B1, B2\right)) \land (\operatorname {euclideanSectionalCurvature}\left(A1, A2, B1, B2\right) = -\frac{1}{2})) \land (\exists A1 \in \operatorname {Matrix}\left(\operatorname {Fin}\left(n - 1\right), \operatorname {Fin}\left(n - 1\right), \operatorname {Real}\right),\; \exists A2 \in \operatorname {Matrix}\left(\operatorname {Fin}\left(n - 1\right), \operatorname {Fin}\left(n - 1\right), \operatorname {Real}\right),\; \exists B1 \in \operatorname {Matrix}\left(\operatorname {Fin}\left(1\right), \operatorname {Fin}\left(n - 1\right), \operatorname {Real}\right),\; \exists B2 \in \operatorname {Matrix}\left(\operatorname {Fin}\left(1\right), \operatorname {Fin}\left(n - 1\right), \operatorname {Real}\right),\; (\operatorname {orthonormalTangentBlocks}\left(A1, A2, B1, B2\right)) \land (\operatorname {euclideanSectionalCurvature}\left(A1, A2, B1, B2\right) = \frac{1}{2}))))\right)$$

*Formalization.* `D5/S3/Geometry/Riemannian/ZimmermannStoyeCodimensionOneCurvature.claim` (`✓ std3`).

*Citation.* Ralf Zimmermann and Jakob Stoye (2024). *High curvature means low-rank: On the sectional curvature of Grassmann and Stiefel manifolds and the underlying matrix trace inequalities*. DOI: [10.1137/24M1655755](https://doi.org/10.1137/24M1655755). URL: <https://arxiv.org/abs/2403.01879v3>.

*Commentary.*

The source states: “For n ≥ 4 and (n, p) = (n, n − 1), sharp bounds on the sectional curvature of the Stiefel manifold under the Euclidean metric are −1/2 ≤ K_e^St(X,Y) ≤ 1/2.” (Conjecture 1, PDF page 17.) Here p=n−1, the bottom blocks have one row, and sharpness means that each endpoint is attained in every such dimension.

**Theorem 1.5 (The sharp interval and both endpoints).**

$$\forall n \in \operatorname {Nat},\; (4 \le n) \Rightarrow ((\forall A1 \in \operatorname {Matrix}\left(\operatorname {Fin}\left(n - 1\right), \operatorname {Fin}\left(n - 1\right), \operatorname {Real}\right),\; \forall A2 \in \operatorname {Matrix}\left(\operatorname {Fin}\left(n - 1\right), \operatorname {Fin}\left(n - 1\right), \operatorname {Real}\right),\; \forall B1 \in \operatorname {Matrix}\left(\operatorname {Fin}\left(1\right), \operatorname {Fin}\left(n - 1\right), \operatorname {Real}\right),\; \forall B2 \in \operatorname {Matrix}\left(\operatorname {Fin}\left(1\right), \operatorname {Fin}\left(n - 1\right), \operatorname {Real}\right),\; (\operatorname {orthonormalTangentBlocks}\left(A1, A2, B1, B2\right)) \Rightarrow ((-\frac{1}{2} \le \operatorname {euclideanSectionalCurvature}\left(A1, A2, B1, B2\right)) \land (\operatorname {euclideanSectionalCurvature}\left(A1, A2, B1, B2\right) \le \frac{1}{2}))) \land ((\exists A1 \in \operatorname {Matrix}\left(\operatorname {Fin}\left(n - 1\right), \operatorname {Fin}\left(n - 1\right), \operatorname {Real}\right),\; \exists A2 \in \operatorname {Matrix}\left(\operatorname {Fin}\left(n - 1\right), \operatorname {Fin}\left(n - 1\right), \operatorname {Real}\right),\; \exists B1 \in \operatorname {Matrix}\left(\operatorname {Fin}\left(1\right), \operatorname {Fin}\left(n - 1\right), \operatorname {Real}\right),\; \exists B2 \in \operatorname {Matrix}\left(\operatorname {Fin}\left(1\right), \operatorname {Fin}\left(n - 1\right), \operatorname {Real}\right),\; (\operatorname {orthonormalTangentBlocks}\left(A1, A2, B1, B2\right)) \land (\operatorname {euclideanSectionalCurvature}\left(A1, A2, B1, B2\right) = -\frac{1}{2})) \land (\exists A1 \in \operatorname {Matrix}\left(\operatorname {Fin}\left(n - 1\right), \operatorname {Fin}\left(n - 1\right), \operatorname {Real}\right),\; \exists A2 \in \operatorname {Matrix}\left(\operatorname {Fin}\left(n - 1\right), \operatorname {Fin}\left(n - 1\right), \operatorname {Real}\right),\; \exists B1 \in \operatorname {Matrix}\left(\operatorname {Fin}\left(1\right), \operatorname {Fin}\left(n - 1\right), \operatorname {Real}\right),\; \exists B2 \in \operatorname {Matrix}\left(\operatorname {Fin}\left(1\right), \operatorname {Fin}\left(n - 1\right), \operatorname {Real}\right),\; (\operatorname {orthonormalTangentBlocks}\left(A1, A2, B1, B2\right)) \land (\operatorname {euclideanSectionalCurvature}\left(A1, A2, B1, B2\right) = \frac{1}{2}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Riemannian/ZimmermannStoyeCodimensionOneCurvature.result` (`✓ std3`). ∎

*Resolves.* `Problems/zs2403` (proved) by `D5/S3/Geometry/Riemannian/ZimmermannStoyeCodimensionOneCurvature.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"zs2403","declaration_gid":"D5/S3/Geometry/Riemannian/ZimmermannStoyeCodimensionOneCurvature.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Ralf Zimmermann and Jakob Stoye (2024). *High curvature means low-rank: On the sectional curvature of Grassmann and Stiefel manifolds and the underlying matrix trace inequalities*. DOI: [10.1137/24M1655755](https://doi.org/10.1137/24M1655755). URL: <https://arxiv.org/abs/2403.01879v3>.

*Commentary.*

The row Gram matrix is diagonalized by an orthogonal change of the tangent-plane basis. A second orthogonal change puts the rows on distinct coordinate axes. The curvature expansion preserves the coupled cross term; the real skew commutator estimate and a scalar two-square deficit give the interval. Fixed coordinate patterns attain both endpoints in every target dimension.

## References

- Truth anchor: `D5/S3/Geometry/Riemannian/ZimmermannStoyeCodimensionOneCurvature.claim`
- Truth anchor: `D5/S3/Geometry/Riemannian/ZimmermannStoyeCodimensionOneCurvature.euclideanSectionalCurvature`
- Truth anchor: `D5/S3/Geometry/Riemannian/ZimmermannStoyeCodimensionOneCurvature.orthonormalTangentBlocks`
- Truth anchor: `D5/S3/Geometry/Riemannian/ZimmermannStoyeCodimensionOneCurvature.result`
- Truth anchor: `D5/S3/Geometry/Riemannian/ZimmermannStoyeCodimensionOneCurvature.stiefel`
- Dependency: [D5/S3/Combinatorics/Graph/KyFanGap/NearExtremal](../../Combinatorics/Graph/KyFanGap/NearExtremal.md)
- Dependency: [D5/S3/Quantum/GNSMatrix](../../Quantum/GNSMatrix.md)

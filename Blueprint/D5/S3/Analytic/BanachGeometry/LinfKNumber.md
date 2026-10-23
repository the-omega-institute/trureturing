# K-sets and the K-number of real sup-norm spaces

## Abstract

For real sup-norm spaces of dimension n ≥ 2, an extreme-point set is a K-set exactly when it spans, and the K-number is n.

Sain, Manna and Paul, arXiv:2407.08900v1, Definition 1: “Definition 1. Let X be a Banach space. A set A ⊂ S_X is said to be a Koldobsky-set, for the sake of brevity, a K-set, if any operator T ∈ L(X) that preserves Birkhoff-James orthogonality at each point of A, is necessarily a scalar multiple of an isometry.”

Definition 3 of the same paper: “Definition 3. Let X be a Banach space having a finite K-set. Then the K-number of X is defined by min{|A| : A is a K-set of X}. We denote the K-number of X by κ(X).”

The Open Question at the end of §2 reads: “Open Question: Characterize the minimal K-sets in ℓ^n_∞ and hence find κ(ℓ^n_∞).” Minimal means minimal under inclusion. The characterization below concerns extreme-point sets; minimal K-sets containing non-extreme points are not classified.

**Definition 1.1 (Birkhoff–James orthogonality).**

$$\operatorname{BJOrth}\left(x, y\right) \Leftrightarrow (\forall t: \mathbb{R}, \left\lVert x \right\rVert \le \left\lVert x + t \cdot y \right\rVert)$$

*Formalization.* `D5/S3/Analytic/BanachGeometry/LinfKNumber.BJOrth` (`✓ std3`).

*Citation.* D. Sain; J. Manna; K. Paul (2024). *On local preservation of orthogonality and its application to isometries*. URL: <https://arxiv.org/abs/2407.08900v1>.

*Commentary.*

For a real seminormed space E, BJOrth x y requires that adding any real multiple of y cannot decrease the norm of x.

**Definition 1.2 (Preservation at a point).**

$$\operatorname{PreservesBJAt}\left(T, x\right) \Leftrightarrow (\forall y: E, (\operatorname{BJOrth}\left(x, y\right)) \Rightarrow (\operatorname{BJOrth}\left(T\left(x\right), T\left(y\right)\right)))$$

*Formalization.* `D5/S3/Analytic/BanachGeometry/LinfKNumber.PreservesBJAt` (`✓ std3`).

*Citation.* D. Sain; J. Manna; K. Paul (2024). *On local preservation of orthogonality and its application to isometries*. URL: <https://arxiv.org/abs/2407.08900v1>.

*Commentary.*

PreservesBJAt T x means that for every y, x ⊥_B y ⇒ Tx ⊥_B Ty. The operator is real linear.

**Definition 1.3 (A scalar multiple of an isometry).**

$$\operatorname{IsScalarMulIsometry}\left(T\right) \Leftrightarrow (\exists c: \mathbb{R}, (0 \le c) \land (\forall y: E, \left\lVert T\left(y\right) \right\rVert = c \cdot \left\lVert y \right\rVert))$$

*Formalization.* `D5/S3/Analytic/BanachGeometry/LinfKNumber.IsScalarMulIsometry` (`✓ std3`).

*Citation.* D. Sain; J. Manna; K. Paul (2024). *On local preservation of orthogonality and its application to isometries*. URL: <https://arxiv.org/abs/2407.08900v1>.

*Commentary.*

The predicate states that one nonnegative real scalar c satisfies ‖T y‖ = c ‖y‖ for every y. It includes T = 0. For c > 0 on the finite-dimensional sup-norm carrier, dividing T by c gives a linear isometry; all linear endomorphisms of that carrier are bounded.

**Definition 1.4 (Koldobsky sets).**

$$\operatorname{IsKSet}\left(A\right) \Leftrightarrow ((A \subseteq \operatorname{sphere}\left(0, 1\right)) \land (\forall T: \operatorname{LinearMap}\left(\mathbb{R}, E, E\right), (\forall x: E, (x \in A) \Rightarrow (\operatorname{PreservesBJAt}\left(T, x\right))) \Rightarrow (\operatorname{IsScalarMulIsometry}\left(T\right))))$$

*Formalization.* `D5/S3/Analytic/BanachGeometry/LinfKNumber.IsKSet` (`✓ std3`).

*Citation.* D. Sain; J. Manna; K. Paul (2024). *On local preservation of orthogonality and its application to isometries*. URL: <https://arxiv.org/abs/2407.08900v1>.

*Commentary.*

IsKSet A requires A to lie on the unit sphere and every real linear operator preserving Birkhoff–James orthogonality at every point of A to scale the norm. In the real finite-dimensional specialization this encodes Definition 1.

**Definition 1.5 (The extreme-point characterization and cardinality bounds).**

$$claim \Leftrightarrow (\forall n: \mathbb{N}, (2 \le n) \Rightarrow ((\forall A: \operatorname{Set}\left(\operatorname{Fin}\left(n\right) \to \mathbb{R}\right), (A \subseteq \operatorname{extremePoints}\left(\mathbb{R}, \operatorname{closedBall}\left(0, 1\right)\right)) \Rightarrow (\operatorname{IsKSet}\left(A\right) \Leftrightarrow (\operatorname{span}\left(\mathbb{R}, A\right) = \operatorname{top}\left(\right)))) \land ((\exists A: \operatorname{Finset}\left(\operatorname{Fin}\left(n\right) \to \mathbb{R}\right), (\operatorname{card}\left(A\right) = n) \land (\operatorname{IsKSet}\left(\operatorname{coe}\left(A\right)\right))) \land (\forall A: \operatorname{Finset}\left(\operatorname{Fin}\left(n\right) \to \mathbb{R}\right), (\operatorname{IsKSet}\left(\operatorname{coe}\left(A\right)\right)) \Rightarrow (n \le \operatorname{card}\left(A\right))))))$$

*Formalization.* `D5/S3/Analytic/BanachGeometry/LinfKNumber.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* D. Sain; J. Manna; K. Paul (2024). *On local preservation of orthogonality and its application to isometries*. URL: <https://arxiv.org/abs/2407.08900v1>.

*Commentary.*

Let X be Fin n → ℝ with the sup norm, V the extreme points of its closed unit ball, and n ≥ 2. The three conjuncts assert that every A ⊆ V is a K-set exactly when its real span is X, that an n-element K-set exists, and that every finite K-set has at least n elements. Together the last two give κ(X) = n under Definition 3. The extreme points are exactly the vectors with every coordinate of absolute value one. Their inclusion-minimal spanning subsets are exactly the bases contained in {±1}ⁿ.

**Theorem 1.6 (Strict descent at active coordinates).**

$$\forall n: \mathbb{N}, \forall w: \operatorname{Function}\left(\operatorname{Fin}\left(n\right), \mathbb{R}\right), \forall z: \operatorname{Function}\left(\operatorname{Fin}\left(n\right), \mathbb{R}\right), ((\neg w = 0) \land (\forall i: \operatorname{Fin}\left(n\right), (\operatorname{abs}\left(w\left(i\right)\right) = \left\lVert w \right\rVert) \Rightarrow (0 < z\left(i\right) \cdot w\left(i\right)))) \Rightarrow (\neg \operatorname{BJOrth}\left(w, z\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/BanachGeometry/LinfKNumber.active_not_BJ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* D. Sain; J. Manna; K. Paul (2024). *On local preservation of orthogonality and its application to isometries*. URL: <https://arxiv.org/abs/2407.08900v1>.

*Commentary.*

For a nonzero finite real coordinate vector w, if zᵢwᵢ is strictly positive at every coordinate where |wᵢ| = ‖w‖, a sufficiently small negative multiple of z decreases every coordinate below ‖w‖. Finiteness gives one common step size. Therefore w is not Birkhoff–James orthogonal to z. This criterion controls the active facets in the image-vertex proof and in the polyhedral plane counterexample.

**Theorem 1.7 (Proof of the characterization and the K-number).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/BanachGeometry/LinfKNumber.result` (`✓ std3`). ∎

*Resolves.* `Problems/sain-manna-paul-2024-linf-k-number` (proved) by `D5/S3/Analytic/BanachGeometry/LinfKNumber.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"sain-manna-paul-2024-linf-k-number","declaration_gid":"D5/S3/Analytic/BanachGeometry/LinfKNumber.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* D. Sain; J. Manna; K. Paul (2024). *On local preservation of orthogonality and its application to isometries*. URL: <https://arxiv.org/abs/2407.08900v1>.

*Commentary.*

At a vertex u, a zero coordinate of y implies u ⊥B y. A kernel vector contradicts preservation at a vertex with nonzero image, so a nonzero operator preserving at a spanning vertex set is injective. The active-coordinate inequality forces every coordinate of T u to have absolute value ‖T u‖. For S = T⁻¹, the proof gives uᵢ Sᵢⱼ (T u)ⱼ ≥ 0. Two nonzero entries in one column would constrain all test vertices to uᵢ = ±uₖ, contradicting span. Thus S has permutation support, and its action on one vertex fixes the common absolute value of its nonzero entries. This proves norm scaling. Conversely a nonzero rank-one operator annihilating a proper span preserves at that set but cannot scale the norm in dimension at least two. Finally, the all-ones vector and the n − 1 vectors obtained by changing one nonzero-index coordinate to −1 form an n-element spanning vertex set. The characterization also implies that any n linearly independent extreme points suffice in these sup-norm spaces.

## References

- Truth anchor: `D5/S3/Analytic/BanachGeometry/LinfKNumber.BJOrth`
- Truth anchor: `D5/S3/Analytic/BanachGeometry/LinfKNumber.IsKSet`
- Truth anchor: `D5/S3/Analytic/BanachGeometry/LinfKNumber.IsScalarMulIsometry`
- Truth anchor: `D5/S3/Analytic/BanachGeometry/LinfKNumber.PreservesBJAt`
- Truth anchor: `D5/S3/Analytic/BanachGeometry/LinfKNumber.active_not_BJ`
- Truth anchor: `D5/S3/Analytic/BanachGeometry/LinfKNumber.claim`
- Truth anchor: `D5/S3/Analytic/BanachGeometry/LinfKNumber.result`

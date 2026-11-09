# Unitary invariant orthogonal weights

## Abstract

Unitary invariance and orthogonal additivity determine nonnegative vector weights.

**Theorem 1.1 (Uniqueness of the squared norm).**

$$\begin{gathered}\forall K: \operatorname{Type}(), H: \operatorname{Type}(),\\{}[\operatorname{RCLike}(K)], [\operatorname{NormedAddCommGroup}(H)], [\operatorname{InnerProductSpace}(K,H)], [\operatorname{CompleteSpace}(H)],\\{}2\leq \operatorname{rank}(K,H), W: H\to \mathbb{R}_{\geq0},\\{}[\forall U: \operatorname{LinearIsometryEquiv}(K,H,H), v: H, W(U(v))= W(v)],\\{}[\forall x: H, y: H, \operatorname{inner}(K,x,y)=0\Rightarrow W(x+y)= W(x)+W(y)],\\{}[\forall u: H, \left\lVert u \right\rVert=1\Rightarrow W(u)=1]\\{}\Rightarrow \forall v: H, \operatorname{coe}(W(v))= \left\lVert v \right\rVert^{2}.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/UnitaryOrthogonalWeight.unitary_orthogonal_weight_eq_norm_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let H be a complete inner-product space over the real or complex numbers, of cardinal dimension at least two. The weight takes values in the nonnegative reals, with no upper bound and no regularity assumption.

Every two vectors of equal norm are related by a linear isometric equivalence. To construct it, extend the singleton-span isometry inside the finite-dimensional span of the two vectors, then act identically on its orthogonal complement. This applies also when H is infinite-dimensional.

Two orthonormal directions give an additive function f on nonnegative squared radii. Nonnegativity makes f monotone. Normalization gives f(1)=1, additivity fixes every nonnegative rational, and rational density then fixes every nonnegative real. Equal-norm transport gives the asserted identity for every vector.

## References

- Truth anchor: `D5/S3/Quantum/Measurements/UnitaryOrthogonalWeight.unitary_orthogonal_weight_eq_norm_sq`

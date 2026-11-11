# The exact boundary of finite three-path queries

## Abstract

Every prescribed finite three-path menu has an explicit smooth positive extension which preserves all tested values and both finite symmetries but fails global balance.

**Theorem 1.1 (An explicit simultaneous countermodel for every finite menu).**

$$\forall (M : \operatorname{Finset}\left(Recipe\right)), \forall (epsilon : \mathbb{R}), (0 < epsilon) \Rightarrow \text{let} S = \operatorname{phaseClosure}\left(\operatorname{biUnion}\left(M, readPoints\right)\right); \exists (q : (\mathbb{C} \to \mathbb{R})), (q = \operatorname{perturbedReadout}\left(S, epsilon\right)) \land (0 \in S) \land (\forall (r : Recipe), (r \in M) \Rightarrow \operatorname{readPoints}\left(r\right) \subseteq S) \land (\operatorname{ContDiff}\left(\mathbb{R}, \infty, q\right)) \land (\forall (z : \mathbb{C}), 0 \le \operatorname{q}\left(z\right)) \land (\forall (z : \mathbb{C}), (z \neq 0) \Rightarrow 0 < \operatorname{q}\left(z\right)) \land (\operatorname{q}\left(0\right) = 0) \land (\forall (z : \mathbb{C}), \operatorname{q}\left(omega \cdot z\right) = \operatorname{q}\left(z\right)) \land (\forall (z : \mathbb{C}), \operatorname{q}\left(-z\right) = \operatorname{q}\left(z\right)) \land (\forall (a : \mathbb{C}), (a \in S) \Rightarrow \operatorname{q}\left(a\right) = \operatorname{NormSq}\left(a\right)) \land (\forall (r : Recipe), (r \in M) \Rightarrow \operatorname{Passes}\left(q, r\right)) \land (\neg\operatorname{Balance}\left(U, q\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/RealThreePathFiniteQueryBoundary.finite_query_boundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix the original real vector space C, with U(z)=omega z and omega=-1/2+i sqrt(3)/2. A recipe r is a triple (x,y,t) in C by C by R. Its readPoints are exactly 0, x, y, tx, ty, x+ty, x+tU(y), and tU(x)+y. For any finite menu M of such recipes, A is the union of their readPoints. S=phaseClosure(A) is the union, over a in A together with zero, of a, omega a, omega squared a, -a, -omega a, and -omega squared a. Thus S is finite, contains zero and every point actually read, and is closed under U and negation. Empty menus are included.

$$
\operatorname{P}\left(z\right) = \prod_{a \in S}\operatorname{NormSq}\left(z - a\right), \operatorname{q}\left(z\right) = \operatorname{NormSq}\left(z\right) + epsilon \cdot (\operatorname{P}\left(z\right))^{2}
$$

The existential q in the statement is required to equal this explicit perturbedReadout(S,epsilon) as a function on the whole original C. The same q supplies every conclusion. ContDiff R infinity q means smoothness in the original two real coordinates. NormSq(z) is the ordinary Euclidean squared modulus. Positivity away from zero is pointwise strict positivity, with no uniform lower bound asserted.

$$
\operatorname{Q}\left(x + t \cdot y\right) + \operatorname{Q}\left(x + t \cdot \operatorname{U}\left(y\right)\right) + \operatorname{Q}\left(t \cdot \operatorname{U}\left(x\right) + y\right) = 2 \cdot \operatorname{Q}\left(x\right) + \operatorname{Q}\left(y\right) + \operatorname{Q}\left(t \cdot x\right) + 2 \cdot \operatorname{Q}\left(t \cdot y\right)
$$

Passes(q,r) means precisely the displayed equation, with Q(z)=q(z)-q(0) throughout. Balance(U,q) quantifies the same equation over all original x,y and every real t. The right side retains Q(tx) and Q(ty) as actual readouts; no squared gain is assumed. The displayed finite-menu statement therefore preserves the original tests and their baseline, rather than substituting a calibrated relation.

The construction is C140 Proposition 4.6. Since omega cubed and NormSq(omega) are one, the six-point orbits are permuted by phase and negation. Reindexing the finite distance product preserves P under both operations. Every a in S contributes a zero factor at a, so q(a)=NormSq(a). In particular q(0)=0. Smoothness follows from finite products of smooth squared distances. The nonnegative squared perturbation preserves nonnegativity and the strict positivity supplied by NormSq away from zero. The standard squared-modulus model satisfies Balance by the existing original Hilbert characterization, so equality of all original tested values preserves every listed test.

For the obstruction, restrict to the real ray. P(t) is the evaluation of the real polynomial R(X), the product over a in S of (X-Re(a)) squared plus Im(a) squared. Each factor is monic of degree two; consequently R squared has degree 4 times the cardinality of S, at least four. If q satisfied global Balance, raw_real_polar would give a real bilinear diagonal, and q(0)=0 would force q(t)=t squared q(1). The explicit perturbation would then imply R(X) squared=((q(1)-1)/epsilon) X squared, since these polynomials agree at every real t. The right side has degree at most two, a contradiction. This uses the frozen polar theorem without reconstructing the representation.

The result concerns unrestricted original real-valued readouts and an arbitrary prescribed finite menu. The countermodel may depend on that menu and epsilon. It does not assert that one fixed nonquadratic readout passes every finite menu, nor does it rule out finite certification within a separately specified finite-dimensional function class. It supplies a mathematical countermodel and makes no claim that the function is a physical preparation or probability law.

## References

- Truth anchor: `D5/S3/QuadraticForms/RealThreePathFiniteQueryBoundary.finite_query_boundary`
- Dependency: [D5/S3/QuadraticForms/RealThreePathRepresentation](RealThreePathRepresentation.md)

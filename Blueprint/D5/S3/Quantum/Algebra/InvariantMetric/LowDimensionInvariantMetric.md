# Lie Algebras with an Invariant Form in Dimension at Most Three

## Abstract

A left-separating invariant bilinear form makes every Lie algebra of dimension at most two abelian, and an invariant form that is positive on nonzero vectors gives every non-abelian real Lie algebra of dimension three a basis, orthonormal for the form, in which the bracket is a positive multiple of the cross product.

**Theorem 1.1 (Dimension at most two).**

$$\forall K \in \operatorname{Type}*,\; \forall L \in \operatorname{Type}*,\; [\operatorname{Field}\left(K\right)],\ [\operatorname{LieRing}\left(L\right)],\ [\operatorname{LieAlgebra}\left(K, L\right)],\ [\operatorname{FiniteDimensional}\left(K, L\right)],\ \forall B \in \operatorname{BilinForm}\left(K, L\right),\; \operatorname{lieInvariant}\left(B, L\right) \Rightarrow \left(\operatorname{SeparatingLeft}\left(B\right) \Rightarrow \left(\operatorname{finrank}\left(K, L\right) \le 2 \Rightarrow \operatorname{IsLieAbelian}\left(L\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/InvariantMetric/LowDimensionInvariantMetric.isLieAbelian_of_finrank_le_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let K be a field and L a finite-dimensional Lie algebra over K. The form written B in the displayed formula is a K-bilinear form on L. It is invariant, lieInvariant(B, L), when B([x,y], z) = -B(y, [x,z]) for all x, y, z in L; no symmetry of B is assumed. It is left separating, SeparatingLeft(B), when the only x with B(x, z) = 0 for every z is x = 0. If moreover finrank(K, L) is at most two, then L is abelian: [x, y] = 0 for all x and y.

Invariance makes a bracket orthogonal to its arguments in the left slot: B([x,y], x) = -B(y, [x,x]) = 0, and B([x,y], y) = -B([y,x], y) = B(x, [y,y]) = 0. Suppose [x, y] is nonzero. Then x is nonzero, and x, y are linearly independent: applying [x, -] to s x + t y = 0 gives t [x, y] = 0, so t = 0 and then s = 0. Two independent vectors in a space of dimension at most two span it, so the linear functional B([x,y], -) vanishes on all of L, and left separation forces [x, y] = 0, a contradiction.

No hypothesis can be dropped. On the two-dimensional non-abelian Lie algebra with basis e, f and [e, f] = f, the zero form is invariant, and over a field of characteristic other than two every invariant form vanishes on f in the left slot: B(f, e) = B([e,f], e) = -B(f, [e,e]) = 0 and B(f, f) = B([e,f], f) = -B(f, [e,f]) = -B(f, f). The standard dot product of the coordinates is left separating but not invariant. Finite dimension is needed because finrank is zero for infinite-dimensional spaces: the cross-product algebra on three-space plus an infinite-dimensional abelian summand, with the dot product on the first summand and any inner product on the second, is a non-abelian example.

**Theorem 1.2 (Dimension three: the cross product).**

$$\forall L \in \operatorname{Type}*,\; [\operatorname{LieRing}\left(L\right)],\ [\operatorname{LieAlgebra}\left(\mathbb{R}, L\right)],\ \forall B \in \operatorname{BilinForm}\left(\mathbb{R}, L\right),\; \operatorname{lieInvariant}\left(B, L\right) \Rightarrow \left(\left(\forall x \in L,\; x \ne 0 \Rightarrow 0 < B\left(x, x\right)\right) \Rightarrow \left(\operatorname{finrank}\left(\mathbb{R}, L\right) = 3 \Rightarrow \left(\left(\neg \operatorname{IsLieAbelian}\left(L\right)\right) \Rightarrow \left(\exists b \in \operatorname{Basis}\left(\operatorname{Fin}\left(3\right), \mathbb{R}, L\right),\; \exists c \in \mathbb{R},\; 0 < c \land \left(\left(\forall i \in \operatorname{Fin}\left(3\right), j \in \operatorname{Fin}\left(3\right),\; B\left(b\left(i\right), b\left(j\right)\right) = \operatorname{if} i=j \operatorname{then} 1 \operatorname{else} 0\right) \land \left(\forall x \in L, y \in L,\; \operatorname{equivFun}\left(b\right)\left([x, y]\right) = c \cdot \operatorname{crossProduct}\left(\operatorname{equivFun}\left(b\right)\left(x\right), \operatorname{equivFun}\left(b\right)\left(y\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/InvariantMetric/LowDimensionInvariantMetric.exists_basis_bracket_eq_smul_cross` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* John Milnor (1976). *Curvatures of left invariant metrics on Lie groups*. DOI: [10.1016/S0001-8708(76)80002-3](https://doi.org/10.1016/S0001-8708(76)80002-3).

*Commentary.*

Let L be a real Lie algebra of dimension three that is not abelian, and B an invariant real bilinear form on L with B(x, x) > 0 for every nonzero x; B is not assumed symmetric. Then there are a basis b of L indexed by Fin 3 and a real number c > 0 such that B(b(i), b(j)) is 1 for i = j and 0 otherwise, and such that for all x and y the coordinate vector of [x, y] in the basis b, written equivFun(b)([x, y]), is c times the cross product of the coordinate vectors of x and y. Evaluating at basis vectors gives [b(0), b(1)] = c b(2), [b(1), b(2)] = c b(0) and [b(2), b(0)] = c b(1). Since B is the identity matrix in the basis b, the conclusion also shows that B is symmetric.

Choose x, y with [x, y] nonzero. Invariance gives B([x,[x,y]], y) = -B([x,y], [x,y]) < 0, so [x, [x, y]] is nonzero as well. Rescale x and [x, y] to vectors e1, e2 of square one; they are orthogonal in both slots because a bracket is orthogonal to its arguments. Their bracket is a positive multiple of a unit vector e3, which is again orthogonal to e1 and e2 in both slots. Three orthonormal vectors are linearly independent and so form a basis, in which the coordinates of z are B(z, e1), B(z, e2), B(z, e3). Invariance then determines the remaining brackets: B([e2,e3], e1) = -B(e3, [e2,e1]) gives [e2, e3] = c e1, and similarly [e3, e1] = c e2. Both sides of the claimed identity are bilinear in x and y and agree on the basis.

The cross-product algebra on three-space with the dot product satisfies all hypotheses, with the standard basis and c = 1. Positivity cannot be weakened to non-degeneracy: on sl(2, R) the Killing form is invariant and non-degenerate but not positive, while the conclusion forces the form to be positive. The zero form on the cross-product algebra is invariant and fails the conclusion, so the form must be positive and not merely invariant. The non-abelian hypothesis is needed, since three-space with the zero bracket and the dot product satisfies the other hypotheses and has no such basis.

Related statements hold under further hypotheses: `D5/S3/Quantum/Algebra/RankOneInvariantMetric.min_frame` gives a frame of this kind and `D5/S3/Quantum/Algebra/RankOneInvariantMetric.finrank_eq_one_or_three` the dimension count, both assuming that the centralizer of a fixed element is a line, and the last clause of `D5/S3/Quantum/Algebra/Comparison/RoundTripClassification.comparison_classification` gives an orthonormal frame of the same kind under the round-trip comparison hypotheses. The present statement assumes neither and uses only invariance, positivity, dimension three and non-commutativity.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/Comparison/RoundTripClassification.comparison_classification`
- Truth anchor: `D5/S3/Quantum/Algebra/InvariantMetric/LowDimensionInvariantMetric.exists_basis_bracket_eq_smul_cross`
- Truth anchor: `D5/S3/Quantum/Algebra/InvariantMetric/LowDimensionInvariantMetric.isLieAbelian_of_finrank_le_two`
- Truth anchor: `D5/S3/Quantum/Algebra/RankOneInvariantMetric.finrank_eq_one_or_three`
- Truth anchor: `D5/S3/Quantum/Algebra/RankOneInvariantMetric.min_frame`

# C117 Fixed Fourteen Projection

## Abstract

The complete original C117 Lemma 46.2: fourteen cubic residuals yield an ambient orthogonal projection of rank one through twenty-four.

H is any complete complex Hilbert space, including infinite-dimensional and nonseparable H. s and t are arbitrary complex-linear isometric equivalences H to H with s t s = t s t. Thus every genuine unitary B3 representation supplies such a pair. v is any vector with norm one. b is any Hilbert basis, with arbitrary index type beta; its existence imposes no extra restriction on H. Set x=(sqrt(5)-1)/2 and a=x^2 in the specified real embedding. cubicOperator(a,s) is exactly s^3-a s^2+a s-I on the original H.

wordEval multiplies the letters in their written algebraic order. The ordered twenty-four orbit words are: 1; s; s^-1; t; t s; t s^-1; s t; s t s; s t s^-1; s^-1 t; s^-1 t s; s^-1 t s^-1; t^-1; t^-1 s; t^-1 s^-1; s t^-1; s t^-1 s; s t^-1 s^-1; s^-1 t^-1; s^-1 t^-1 s; s^-1 t^-1 s^-1; t^-1 s t^-1; s t^-1 s t^-1; s^-1 t^-1 s t^-1. The synthesis map takes standard basis vector j to wordEval(q_j)v. No linear independence is assumed.

The ordered fourteen tails are exactly: 1; t; t s; t s^-1; t^-1; t^-1 s; t^-1 s^-1; t^-1 s t^-1; t^-1 s^-2; t^-2 s^-1; t^-2; t^-1 s^-3; s^-1; t^-2 s^-2. delta is the maximum over these fourteen tails of norm(cubicOperator(a,s) wordEval(h)v). columns and errors retain all forty-eight source columns and every listed residual triple, including all seventeen terms of t column twelve. environment_columns proves these identities directly from the braid relation for arbitrary complex a, rather than assuming the source prose.

For S a finite-dimensional subspace of the original H, E=S.starProjection is the actual orthogonal projection H to H. projectionDefect(S,g)=g E g^-1-E. defect(b,S,s,t) is sqrt((1/2) sum over g=s,t of sum over l in beta of norm(projectionDefect(S,g)(b_l))^2). The square sums are summable, and each ambient defect is certified Hilbert-Schmidt, so this is the genuine D(E) in the original lemma.

**Theorem 1.1 (Condition-free bounded-rank projection).**

$$\forall b\in \operatorname{HilbertBasis}(beta, H), s,t\in \operatorname{Unitary}(H), sts=tst\Rightarrow \forall v\in H, \Vert v\Vert =1\Rightarrow \exists S\in \operatorname{Subspace}(H), \operatorname{FiniteDimensional}(S)\land \operatorname{OrthogonalProjection}(\operatorname{starProjection}(S))\land \operatorname{range}(\operatorname{starProjection}(S))=S\land 1\le \operatorname{dim}(S)\le 24\land (\forall g\in \operatorname{pair}(s, t), \operatorname{IsHilbertSchmidt}(\operatorname{projectionDefect}(S, g))\land \operatorname{Summable}(\operatorname{ambientSquareSum}(b, S, g)))\land (0< delta< 1\Rightarrow \operatorname{defect}(b, S, s, t)\le 785(delta)^{\frac{1}{24}})\land (delta=0\Rightarrow \operatorname{defect}(b, S, s, t)=0\land \forall g\in \operatorname{pair}(s, t), \operatorname{projectionDefect}(S, g)=0)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hilbert/C117FixedFourteenProjection.condition_free_projection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The explicit matrix column coefficient sums are at most thirteen. The at-most-seventeen residual terms per column have coefficients of norm at most one and their right tails all belong to the exact fourteen-tail list. The proved identities give operator bounds norm(M_g)<=85 and norm(gT-TM_g)<=95 delta. FiniteSynthesisSpectralCut selects the first geometric singular gap without a gap hypothesis, normalizes only positive selected singular vectors and estimates their ambient leakage. FiniteRankUnitaryDefect proves the ambient Hilbert-Schmidt square-sum identity and uses eta=(6/5) delta^(1/24), with a separate contraction estimate for large delta, to obtain 785. At delta=0, the nonzero finite synthesis range is invariant; its unitary image has the same finite dimension and therefore equals the range. Its orthogonal projection commutes with both generators. There is no finite ambient, invariant ambient, singular-gap, independent-column or Gram-inverse premise. This proves Lemma 46.2 only; Theorem 46.5 and numerical coercivity remain outside this result. The orbit architecture and parameter tables reuse the supplied Marin, The cubic Hecke algebra on at most 5 strands, arXiv:1110.6621v1, section 2, Lemmas 2.1, 2.3, 2.4 and Theorem 3.2(4), and are not counted as new mathematical content.

## References

- Truth anchor: `D5/S3/Observer/Hilbert/C117FixedFourteenProjection.condition_free_projection`
- Dependency: [D5/S3/Observer/Hilbert/FiniteRankUnitaryDefect](FiniteRankUnitaryDefect.md)

# An Invariant Metric on the Original Compact Action

## Abstract

The original compact matrix action supplies an invariant positive form on the same prediction space.

**Theorem 1.1 (Compactness supplies the metric and skew curve velocities).**

$$\forall W,G,\ \operatorname{FiniteDimensionalRealInnerProductSpace}\left(W\right) \land \operatorname{SubgroupOfUnitsEnd}\left(G, W\right) \land \operatorname{IsCompact}\left(G\right) \Rightarrow \exists B:\operatorname{InnerProductSpaceCore}\left(\mathbb{R}, W\right),\ (\forall h:G,\ \forall u,v:W,\ \operatorname{B}\left(\operatorname{h}\left(u\right), \operatorname{h}\left(v\right)\right)=\operatorname{B}\left(u, v\right)) \land \forall c:\mathbb{R} \Rightarrow G,\ \operatorname{c}\left(0\right)=1 \Rightarrow \forall K:\operatorname{End}\left(\mathbb{R}, W\right),\ \operatorname{HasDerivAt}\left(\operatorname{originalOperatorCurve}\left(c\right), K, 0\right) \Rightarrow \forall u,v:W,\ \operatorname{B}\left(\operatorname{K}\left(u\right), v\right)=-\operatorname{B}\left(u, \operatorname{K}\left(v\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/OriginalCompactActionMetric.compact_action_metric` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let W be any finite-dimensional real inner product space, including the zero space. Its initially chosen inner product is auxiliary and need not be invariant. Let G be any subgroup of the units of the continuous real endomorphism algebra of that same W, with compact underlying set in the inherited operator topology. Thus the action is the original faithful matrix action; no new representation or smaller invariant subspace is substituted. Compactness is the only additional hypothesis of the theorem.

There exists a positive definite symmetric real bilinear form B on W, encoded by InnerProductSpace.Core, invariant under every member of G. For every actual curve c from the real line to G with c(0)=1, and every ambient operator K which is the derivative at zero of the original operator-valued curve, B(Ku,v)=-B(u,Kv) for every u,v in the full W. The curve is not assumed to be a chosen exponential or an abstract Lie-algebra witness.

The proof integrates the operators g-inverse-adjoint composed with g-inverse against left Haar measure on the actual compact subgroup. The resulting Gram operator S represents B(u,v)=inner(u,Sv). Continuous integrands on the compact group are integrable; the diagonal is nonnegative and its value at the identity is strictly positive for a nonzero vector, so Haar positivity makes B definite. Left translation proves invariance. Differentiating that identity along the actual G-valued curve gives skewness.

The Gram construction is an adapted port of TauCeti's compact representation unitarization at immutable revision 57ab0f657d7fb33d7c9425bf696bec3045b0fd75, file TauCeti/RepresentationTheory/Compact/Unitarizable.lean. The original copyright and full Apache 2.0 license are retained in Lean. The inverse action avoids importing its Haar-probability infrastructure. This is an application and a source bridge, with no originality claim for Haar unitarization.

This is the metric dependency in OMEGAQ-008 Theorem 5.1. It does not assert that the original complete quotient relation holds, supply that theorem's dimension conclusion, identify a group component, classify G as SO or O, or prove the complete original rigidity equivalence. The finite-dimensional hypothesis provides the complete operator space used for integration; no parity, nonzero vector, rank, centralizer, transitivity or irreducibility assumption is added.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/OriginalCompactActionMetric.compact_action_metric`

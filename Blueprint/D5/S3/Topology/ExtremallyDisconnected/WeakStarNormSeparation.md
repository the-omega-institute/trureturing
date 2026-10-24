# Uniform strong-dual norm separation

## Abstract

Compact Stonean weak-star embeddings have a uniform positive operator-norm gap.

**Theorem 1.1 (Exact separation theorem).**

$$\begin{aligned}\forall u: UniverseLevel, \forall v: UniverseLevel, \\\forall X: Type_{u}, [\operatorname{NormedAddCommGroup}\left(X\right)] [\operatorname{NormedSpace}\left(Real, X\right)] \\\forall K: Type_{v}, [\operatorname{TopologicalSpace}\left(K\right)] [\operatorname{CompactSpace}\left(K\right)] [\operatorname{T2Space}\left(K\right)] [\operatorname{ExtremallyDisconnected}\left(K\right)] \\\forall h: K \to \operatorname{WeakDual}\left(Real, X\right), \operatorname{Continuous}\left(h\right) \Rightarrow \operatorname{Injective}\left(h\right) \Rightarrow \\\exists c: Real, 0 < c \land \forall p: K, \forall q: K, p \neq q \Rightarrow c \le \operatorname{norm}\left(\operatorname{WeakDual.toStrongDual}\left({\operatorname{h}\left(p\right) - \operatorname{h}\left(q\right)}\right)\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/ExtremallyDisconnected/WeakStarNormSeparation.exists_pos_le_norm_sub` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

X is any real normed space, and K is any compact Hausdorff extremally disconnected space. The map h is continuous for the weak-star topology and injective. There is one real c greater than zero bounding below the strong-dual norm of h(p)-h(q) for every pair of distinct points. K may be empty or a singleton; neither completeness of X nor a global norm bound is assumed.

More generally, a lower semicontinuous real function F on K times K that is positive away from the diagonal has a uniform positive lower bound there. Otherwise choose unequal pairs with F less than 1/(n+1). For a fixed clopen U, its symmetric cross (U times its complement) union (its complement times U) is compact. If nonempty, F attains a strictly positive minimum on this cross. The chosen pair eventually misses the cross, since 1/(n+1) tends to zero. If the cross is empty it is always missed. Thus membership in every clopen eventually agrees. PointPairSeparation.eventually_eq_of_eventually_mem_isClopen_iff forces eventual equality, a contradiction. Symmetry and the triangle inequality for F are not needed.

For the norm theorem, subtraction is continuous in the weak-star topology. Pinned Mathlib's WeakDual.isClosed_closedBall makes every norm sublevel set of the difference closed. This proves lower semicontinuity without asserting continuity of WeakDual.toStrongDual. Injectivity of h and of the linear equivalence toStrongDual gives strict positivity off the diagonal.

The compact-minimum composition is derived here from the supplied ordinary argument and the point-pair theorem. The CH/Talagrand research context is described in Library/Topology/kania2026talagrand.md. This theorem concerns arbitrary dual functionals, including both signs. It does not construct the CH recursion, the signed dual ball, or the full analytic endpoint.

## References

- Truth anchor: `D5/S3/Topology/ExtremallyDisconnected/WeakStarNormSeparation.exists_pos_le_norm_sub`
- Dependency: [D5/S3/Topology/ExtremallyDisconnected/PointPairSeparation](PointPairSeparation.md)

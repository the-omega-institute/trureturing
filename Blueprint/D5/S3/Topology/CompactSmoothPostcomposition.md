# Smooth postcomposition in the uniform norm

## Abstract

Nonlinear postcomposition preserves every finite differentiability order and smoothness on continuous maps from an arbitrary compact topological space.

ContinuousMap(K,E) denotes continuous maps with their existing sup norm. K is any compact topological space, including empty and infinite spaces. The field k is nontrivially normed; the differentiability results also assume IsRCLikeNormedField(k). E and F are normed k-spaces. The independent universe levels are a for K, b for k, u for E, and max(u,v) for F in the differentiability results. No completeness, finite dimension, Hausdorff assumption on K, globally bounded derivative, or linearity of f is required. The bilinear operator and its evaluation identity allow independent E and F universes.

**Definition 1.1 (Bounded pointwise application).**

$$\begin{aligned}\forall K: \operatorname{Type}\left(a\right), [\operatorname{TopologicalSpace}\left(K\right)] [\operatorname{CompactSpace}\left(K\right)] \\\forall k: \operatorname{Type}\left(b\right), [\operatorname{NontriviallyNormedField}\left(k\right)] \\\forall E: \operatorname{Type}\left(u\right), [\operatorname{NormedAddCommGroup}\left(E\right)] [\operatorname{NormedSpace}\left(k, E\right)] \\\forall F: \operatorname{Type}\left(v\right), [\operatorname{NormedAddCommGroup}\left(F\right)] [\operatorname{NormedSpace}\left(k, F\right)] \\\operatorname{applyContinuousLinearMap}\left(\right): \operatorname{ContinuousLinearMap}\left(k, \operatorname{ContinuousMap}\left(K, \operatorname{ContinuousLinearMap}\left(k, E, F\right)\right), \operatorname{ContinuousLinearMap}\left(k, \operatorname{ContinuousMap}\left(K, E\right), \operatorname{ContinuousMap}\left(K, F\right)\right)\right)\end{aligned}$$

*Formalization.* `D5/S3/Topology/CompactSmoothPostcomposition.applyContinuousLinearMap` (`✓ std3`).

*Citation.* The Tau Ceti contributors (2026). *Calculus on spaces of continuous maps*. URL: <https://github.com/TauCetiProject/TauCeti/blob/3924e3ef4afb8102b6a8e9893043c2c1a303f0d1/TauCeti/Analysis/Calculus/ContinuousMap.lean>.

*Commentary.*

For A a continuous family of continuous linear maps and g a continuous E-valued map, applyContinuousLinearMap(A)(g) sends x to A(x)(g(x)). The pointwise operator-norm estimate bounds its uniform norm by the product of the uniform norms of A and g. The resulting operator is continuous linear in A and continuous linear in g.

**Theorem 1.2 (Evaluation of the bilinear operator).**

$$\begin{aligned}\forall K: \operatorname{Type}\left(a\right), [\operatorname{TopologicalSpace}\left(K\right)] [\operatorname{CompactSpace}\left(K\right)] \\\forall k: \operatorname{Type}\left(b\right), [\operatorname{NontriviallyNormedField}\left(k\right)] \\\forall E: \operatorname{Type}\left(u\right), [\operatorname{NormedAddCommGroup}\left(E\right)] [\operatorname{NormedSpace}\left(k, E\right)] \\\forall F: \operatorname{Type}\left(v\right), [\operatorname{NormedAddCommGroup}\left(F\right)] [\operatorname{NormedSpace}\left(k, F\right)] \\\forall A: \operatorname{ContinuousMap}\left(K, \operatorname{ContinuousLinearMap}\left(k, E, F\right)\right), \forall g: \operatorname{ContinuousMap}\left(K, E\right), \forall x: K, \\\operatorname{apply}\left(\operatorname{applyContinuousLinearMap}\left(A\right), g, x\right) = \operatorname{apply}\left(\operatorname{apply}\left(A, x\right), \operatorname{apply}\left(g, x\right)\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/CompactSmoothPostcomposition.applyContinuousLinearMap_apply` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors (2026). *Calculus on spaces of continuous maps*. URL: <https://github.com/TauCetiProject/TauCeti/blob/3924e3ef4afb8102b6a8e9893043c2c1a303f0d1/TauCeti/Analysis/Calculus/ContinuousMap.lean>.

*Commentary.*

Evaluation at every x agrees with actual application of A(x) to g(x). This identity identifies the pointwise derivative in the uniform remainder estimate.

**Theorem 1.3 (Frechet derivative of nonlinear postcomposition).**

$$\begin{aligned}\forall K: \operatorname{Type}\left(a\right), [\operatorname{TopologicalSpace}\left(K\right)] [\operatorname{CompactSpace}\left(K\right)] \\\forall k: \operatorname{Type}\left(b\right), [\operatorname{NontriviallyNormedField}\left(k\right)] [\operatorname{IsRCLikeNormedField}\left(k\right)] \\\forall E: \operatorname{Type}\left(u\right), [\operatorname{NormedAddCommGroup}\left(E\right)] [\operatorname{NormedSpace}\left(k, E\right)] \\\forall F: \operatorname{Type}\left(\operatorname{max}\left(u, v\right)\right), [\operatorname{NormedAddCommGroup}\left(F\right)] [\operatorname{NormedSpace}\left(k, F\right)] \\\forall f: \operatorname{ContinuousMap}\left(E, F\right), \operatorname{ContDiff}\left(k, 1, f\right) \Rightarrow\\\forall g: \operatorname{ContinuousMap}\left(K, E\right), \operatorname{HasFDerivAt}\left({g \mapsto \operatorname{comp}\left(f, g\right)}, \operatorname{applyContinuousLinearMap}\left(\operatorname{comp}\left(\operatorname{bundle}\left(\operatorname{fderiv}\left(k, f\right)\right), g\right)\right), g\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/CompactSmoothPostcomposition.hasFDerivAt_postcomp` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors (2026). *Calculus on spaces of continuous maps*. URL: <https://github.com/TauCetiProject/TauCeti/blob/3924e3ef4afb8102b6a8e9893043c2c1a303f0d1/TauCeti/Analysis/Calculus/ContinuousMap.lean>.

*Commentary.*

In this formula bundle(fderiv(k,f)) is the continuous map from E to continuous linear maps E to F, with continuity supplied by ContDiff(k,1,f). The derivative at g applies fderiv(k,f,g(x)) to the increment at x. Compactness of the image of g and continuity of fderiv give a common neighborhood on which the derivative varies by at most any prescribed positive c. The segment mean-value estimate gives the nonlinear remainder bound c times the uniform input distance. This is the Frechet little-o criterion.

**Theorem 1.4 (Full nonlinear smooth-superposition theorem).**

$$\begin{aligned}\forall K: \operatorname{Type}\left(a\right), [\operatorname{TopologicalSpace}\left(K\right)] [\operatorname{CompactSpace}\left(K\right)] \\\forall k: \operatorname{Type}\left(b\right), [\operatorname{NontriviallyNormedField}\left(k\right)] [\operatorname{IsRCLikeNormedField}\left(k\right)] \\\forall E: \operatorname{Type}\left(u\right), [\operatorname{NormedAddCommGroup}\left(E\right)] [\operatorname{NormedSpace}\left(k, E\right)] \\\forall F: \operatorname{Type}\left(\operatorname{max}\left(u, v\right)\right), [\operatorname{NormedAddCommGroup}\left(F\right)] [\operatorname{NormedSpace}\left(k, F\right)] \\\forall n: \operatorname{NatInfinity}\left(\right), \forall f: \operatorname{ContinuousMap}\left(E, F\right), \\\operatorname{ContDiff}\left(k, \operatorname{toOrder}\left(n\right), f\right) \Rightarrow \operatorname{ContDiff}\left(k, \operatorname{toOrder}\left(n\right), {g \mapsto \operatorname{comp}\left(f, g\right)}\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/CompactSmoothPostcomposition.contDiff_postcomp` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors (2026). *Calculus on spaces of continuous maps*. URL: <https://github.com/TauCetiProject/TauCeti/blob/3924e3ef4afb8102b6a8e9893043c2c1a303f0d1/TauCeti/Analysis/Calculus/ContinuousMap.lean>.

*Commentary.*

NatInfinity consists of the natural orders and infinity; toOrder is its canonical inclusion into NatInfinityOmega, the order type used by ContDiff. The lambda variable g ranges over ContinuousMap(K,E), so Post is a map into ContinuousMap(K,F). Order zero follows from continuity of postcomposition. For a successor order, apply the finite-order induction to the continuous derivative family, then compose with the bounded pointwise application operator. The displayed Frechet derivative identifies this derivative with that of postcomposition. The all-finite-orders criterion gives the infinite case. The max(u,v) codomain universe retains the derivative family at the same universe level.

These are the original selected proofs of the cited source. The nonlinear theorem is a supplier for smooth Picard residuals. It asserts no ODE existence, global-flow, half-density group, strong-continuity, generator, transport-equation or self-adjointness result.

## References

- Truth anchor: `D5/S3/Topology/CompactSmoothPostcomposition.applyContinuousLinearMap`
- Truth anchor: `D5/S3/Topology/CompactSmoothPostcomposition.applyContinuousLinearMap_apply`
- Truth anchor: `D5/S3/Topology/CompactSmoothPostcomposition.contDiff_postcomp`
- Truth anchor: `D5/S3/Topology/CompactSmoothPostcomposition.hasFDerivAt_postcomp`

# Compact Root Coherence

## Abstract

Compactness turns separate positive roots into one coherent rational homomorphism.

**Theorem 1.1 (Positive roots and rational homomorphisms are equivalent).**

$$\forall H: \operatorname{Type}(u), [\operatorname{Group}(H)] [\operatorname{TopologicalSpace}(H)] [\operatorname{IsTopologicalGroup}(H)] [\operatorname{T2Space}(H)] [\operatorname{CompactSpace}(H)] \forall h: H, {\forall n: \mathbb{N}, 0 < n \Rightarrow \exists x: H, x^{n} = h} \iff {\exists phi: \operatorname{MonoidHom}(\operatorname{Multiplicative}(\mathbb{Q}), H), \operatorname{phi}(\operatorname{ofAdd}(1)) = h}.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/CompactRootCoherence.exists_all_positive_roots_iff_exists_rat_hom` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an arbitrary compact Hausdorff topological group H and h in H, the existence of a positive n-th root of h for every positive natural n is equivalent to one algebraic homomorphism from the additive rationals, represented as Multiplicative Q, sending one to h.

The forward direction puts all rational-valued functions into the compact product H^Q. Each finite set of rational coordinates has a nonempty closed constraint set: a single D-th root of h supplies the values, and denominator clearing makes the finite addition equations hold inside its cyclic subgroup. Compactness then supplies a point in every finite constraint set, which is a global homomorphism. Hausdorffness is used for the closed equalizers.

The reverse direction evaluates the homomorphism at 1 divided by n and applies its power map. No topology on Q, continuity, connectedness, Lie structure, faithfulness, or commutativity of H is asserted.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/CompactRootCoherence.exists_all_positive_roots_iff_exists_rat_hom`

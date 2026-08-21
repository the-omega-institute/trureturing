# Permanent Stability of the Centered-Effect Tower

## Abstract

One-step stability of a centered-effect Heisenberg tower is permanent.

**Theorem 1.1 (One-step Heisenberg tower stability is permanent).**

$$\forall d, r, m: \operatorname{Nat},\\{}H: \operatorname{LinearMap}(\mathbb{R}, \operatorname{HermitianTraceZero}(d), \operatorname{HermitianTraceZero}(d)), E: \operatorname{Fin}(r+1) \to\operatorname{HermitianTraceZero}(d),\\{}\operatorname{towerSpace}(H, E, m) = \operatorname{towerSpace}(H, E, m+1) \Rightarrow\\{}((\forall s\in \mathbb{N}, \operatorname{towerSpace}(H, E, m+s) = \operatorname{towerSpace}(H, E, m)) \land\\{}((\forall s\in \mathbb{N}, \operatorname{residualSpace}(H, E, m+s) = \operatorname{residualSpace}(H, E, m))).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/CenteredEffectTowerStability.heisenberg_tower_once_stable_permanently` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The carrier is the real HermitianTraceZero(d) subspace imported from the readout-fiber family. The effect family is the source's finite centered effect family and the real-linear map is its Heisenberg dual action on that carrier.

The visible stage V_n is constructed recursively from the initial real span and the image of the preceding stage under the Heisenberg map. The residual stage R_n is V_n orthogonal complement.

If V_m equals V_(m+1), the recursion has no new image at stage m. Induction gives equality of every later visible stage, and applying orthogonal-complement congruence gives the matching residual equality.

## References

- Truth anchor: `D5/S3/Quantum/Fibers/CenteredEffectTowerStability.heisenberg_tower_once_stable_permanently`
- Dependency: [D5/S3/Quantum/Fibers/TraceZeroReadoutOrthogonalEquivalence](TraceZeroReadoutOrthogonalEquivalence.md)

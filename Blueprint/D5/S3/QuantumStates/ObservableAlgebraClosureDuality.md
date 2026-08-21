# Stable Relations and Observable Algebra Closure

## Abstract

Finite relation fibers and iterated pullbacks generate exactly the stable fiber algebra.

**Theorem 1.1 (The iterated pullback algebra equals the stable fiber algebra).**

$$\forall Y: \operatorname{Type}, [\operatorname{Finite}(Y)], R: Y \to Y \to Prop, tau: Y \to Y, \operatorname{Equivalence}(R) \Rightarrow \operatorname{koopmanClosure}(R, tau) = \operatorname{fiberStarAlgebra}(\operatorname{stableRelation}(R, tau)).$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumStates/ObservableAlgebraClosureDuality.koopman_closure_eq_stable_fiber_algebra` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The fiber star algebra is constructed from complex-valued functions constant on the source equivalence relation and closed under the pointwise star operation. The stable relation requires agreement after every finite iterate of the transition.

The pullback star closure is generated from actual iterates of source-fiber functions. Finite separating indicators prove the reverse inclusion, so the target equality is derived rather than used as a definition.

Repository and pinned-Mathlib searches found no exact packaged theorem. The proof directly applies StarAlgebra.adjoin_le, StarAlgebra.subset_adjoin, StarSubalgebra.prod_mem, StarSubalgebra.sum_mem, Quotient.sound, and Quotient.exact.

## References

- Truth anchor: `D5/S3/QuantumStates/ObservableAlgebraClosureDuality.koopman_closure_eq_stable_fiber_algebra`

# Global Reflection and Relative Coherence

## Abstract

Critical-line localization splits into global reflection closure and relative coherence of the transverse zero support.

**Definition 1.1 (Transverse zero support).**

Lean statement: `D5/S3/Zeros/Symmetry/RiemannGlobalRelativeSplit.transverseSupport`

*Formalization.* `D5/S3/Zeros/Symmetry/RiemannGlobalRelativeSplit.transverseSupport` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This set contains exactly the real displacements from one half of the nontrivial zeta zeros in the open critical strip.

**Definition 1.2 (Global reflection closure).**

Lean statement: `D5/S3/Zeros/Symmetry/RiemannGlobalRelativeSplit.GlobalEvenRiemannHypothesis`

*Formalization.* `D5/S3/Zeros/Symmetry/RiemannGlobalRelativeSplit.GlobalEvenRiemannHypothesis` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every displacement in the transverse support has its negative in the same support.

**Definition 1.3 (One-observer relative coherence).**

Lean statement: `D5/S3/Zeros/Symmetry/RiemannGlobalRelativeSplit.OneObserverRiemannHypothesis`

*Formalization.* `D5/S3/Zeros/Symmetry/RiemannGlobalRelativeSplit.OneObserverRiemannHypothesis` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The transverse support is subsingleton, so any two nontrivial zeros have the same horizontal reading.

**Theorem 1.4 (Critical-line localization splits into two support laws).**

$$\operatorname{RiemannHypothesis} \Leftrightarrow \left(\left(\forall d \in \mathbb{R},\; d \in transverseSupport \Rightarrow -d \in transverseSupport\right) \land \operatorname{Subsingleton}(transverseSupport)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Symmetry/RiemannGlobalRelativeSplit.riemann_hypothesis_iff_global_even_and_one_observer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Critical-line localization makes every transverse displacement zero, which proves both reflection closure and relative coherence.

Conversely, reflection closure places both a displacement and its negative in the support. Relative coherence identifies them, forcing the displacement to vanish. The functional-equation reduction then covers every classical nontrivial zeta zero.

## References

- Truth anchor: `D5/S3/Zeros/Symmetry/RiemannGlobalRelativeSplit.GlobalEvenRiemannHypothesis`
- Truth anchor: `D5/S3/Zeros/Symmetry/RiemannGlobalRelativeSplit.OneObserverRiemannHypothesis`
- Truth anchor: `D5/S3/Zeros/Symmetry/RiemannGlobalRelativeSplit.riemann_hypothesis_iff_global_even_and_one_observer`
- Truth anchor: `D5/S3/Zeros/Symmetry/RiemannGlobalRelativeSplit.transverseSupport`
- Dependency: [D5/S3/Weil/ZetaBridge/RightHalfStripRiemannReduction](../../Weil/ZetaBridge/RightHalfStripRiemannReduction.md)

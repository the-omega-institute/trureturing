# Finite occurrence cycles yield a natural epoch potential

## Abstract

Computed occurrence potentials for native epoch transport

Finite occurrence positions are enumerated directly from every original equation. The resulting graph keeps loops, parallel edges, repeated occurrences, disconnected states, empty systems, signed exponent differences and equations with undefined heads.

**Theorem 1.1 (Cycle criterion and computed potential).**

$$\forall n: Nat, (\forall k: Nat, (\forall m: Nat, (\forall I: \operatorname{EpochInput}\left(n, k, m\right), ((\operatorname{CycleCondition}\left(I\right) \iff \exists s: \operatorname{Fin}\left(m\right) \to Nat, (\operatorname{Potential}\left(I, s\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeComputedEpochPotential.cycleCondition_iff_potential` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The graph reverses an occurrence edge so its max-plus potential inequality is exactly the natural difference inequality. A potential telescopes around every closed walk. Conversely, the finite max-plus construction supplies a real potential, integer flooring preserves the integer-weight inequalities, and one finite input-derived offset establishes every nonnegativity and defined-head lower bound. The recursive ShiftLegal predicate is then proved by induction over the actual expression syntax, including ordered pairs and repeated occurrences.

**Theorem 1.2 (The computed potential feeds the original solution correspondence).**

$$\forall n: Nat, (\forall k: Nat, (\forall m: Nat, (\forall I: \operatorname{EpochInput}\left(n, k, m\right), ((\operatorname{CycleCondition}\left(I\right) \implies \exists s: \operatorname{Fin}\left(m\right) \to Nat, ((\operatorname{Potential}\left(I, s\right) \land \forall p: \operatorname{Fin}\left(n\right) \to Nat, (\forall w: \operatorname{Fin}\left(m\right) \to CompletionTree, (((\operatorname{Legal}\left(\operatorname{functionalInput}\left(I, s\right), p\right) \land (\operatorname{SourceSatisfies}\left(\operatorname{functionalInput}\left(I, s\right), p, w\right) \land \operatorname{SourcePasses}\left(\operatorname{functionalInput}\left(I, s\right), p, w\right))) \iff \exists! v: \operatorname{Fin}\left(m\right) \to CompletionTree, ((\operatorname{OriginalAdmissible}\left(I, p, v\right) \land \operatorname{imageValues}\left(s, v\right) = w))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeComputedEpochPotential.cycleCondition_gives_epoch_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the cycle condition, the computed tuple is passed directly to the existing exact epoch correspondence. Literal transformed evaluation, all state-image filters, every additional filter, undefined states and every original reconstruction therefore remain in the same fixed parameter relation. The independent finite-exception prefix and rigidity clauses are inherited through the existing consumer.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeComputedEpochPotential.cycleCondition_gives_epoch_transport`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeComputedEpochPotential.cycleCondition_iff_potential`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeOriginalReconstructionBridge](NativeOriginalReconstructionBridge.md)
- Dependency: [D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierDual](../../../../Combinatorics/Graph/LayeredCirculation/SupplierDual.md)

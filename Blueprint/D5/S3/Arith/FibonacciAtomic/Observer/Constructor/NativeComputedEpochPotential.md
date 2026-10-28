# Finite occurrence cycles yield a natural epoch potential

## Abstract

Computed occurrence potentials for native epoch transport

Finite occurrence positions are enumerated directly from every original equation. The resulting graph keeps loops, parallel edges, repeated occurrences, disconnected states, empty systems, signed exponent differences and equations with undefined heads.

**Definition 1.1 (An input-only terminating natural tuple program).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeComputedEpochPotential.computedPotential`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeComputedEpochPotential.computedPotential` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every n, k and m and every input I : EpochInput n k m, computedPotential I has type Fin m → Nat. Its integer precursor computedSignedPotential I is the m-th relaxation iterate. The zero iterate d_i is a_i when equation i is defined and zero otherwise. The next iterate at i is the maximum of d_i and all preceding values at j plus a_i-b for each syntax-position occurrence of rho^b X_j in equation i. Each round scans the finite indexed occurrence list; the natural round counter decreases structurally. The output is defined even when the cycle criterion fails, with correctness conditional on that criterion.

**Definition 1.2 (The computed tuple and its correctness certificate).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeComputedEpochPotential.constructPotential`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeComputedEpochPotential.constructPotential` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every input I and proof hcycle : CycleCondition I, constructPotential I hcycle returns the subtype {s : Fin m → Nat // Potential I s}. Its value is definitionally computedPotential I. Nonnegativity comes from the initial lower bounds; a maximizing finite walk and nonpositive cycle deletion prove the edge inequalities after m rounds. Only the proof component uses the cycle condition. The tuple itself needs no additional mathematical witness.

**Theorem 1.3 (Cycle criterion and computed potential).**

$$\forall n: Nat, (\forall k: Nat, (\forall m: Nat, (\forall I: \operatorname{EpochInput}\left(n, k, m\right), ((\operatorname{CycleCondition}\left(I\right) \iff \exists s: \operatorname{Fin}\left(m\right) \to Nat, (\operatorname{Potential}\left(I, s\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeComputedEpochPotential.cycleCondition_iff_potential` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The graph reverses an occurrence edge so its max-plus potential inequality is exactly the natural difference inequality. A potential telescopes around every closed walk. Conversely, initialize each defined head at its nonnegative head exponent and each undefined state at zero. In each round, replace each value by the maximum of its initial lower bound and the preceding source value plus the signed weight over every incoming occurrence edge. After exactly as many rounds as there are states, the resulting integer tuple is nonnegative and satisfies every edge inequality. Every finite-round value is attained by a walk; removing nonpositive cycles gives a simple path with fewer edges than states, proving that the fixed finite bound suffices. Taking natural values therefore computes the required tuple solely from the original equations and head powers, without any supplied potential, parameter assignment or prefix depth. The empty input produces the empty tuple. The recursive ShiftLegal predicate is then proved by induction over the actual expression syntax, including ordered pairs and repeated occurrences.

**Theorem 1.4 (The computed potential feeds the original solution correspondence).**

$$\forall n: Nat, (\forall k: Nat, (\forall m: Nat, (\forall I: \operatorname{EpochInput}\left(n, k, m\right), ((\operatorname{CycleCondition}\left(I\right) \implies \exists s: \operatorname{Fin}\left(m\right) \to Nat, ((\operatorname{Potential}\left(I, s\right) \land \forall p: \operatorname{Fin}\left(n\right) \to Nat, (\forall w: \operatorname{Fin}\left(m\right) \to CompletionTree, (((\operatorname{Legal}\left(\operatorname{functionalInput}\left(I, s\right), p\right) \land (\operatorname{SourceSatisfies}\left(\operatorname{functionalInput}\left(I, s\right), p, w\right) \land \operatorname{SourcePasses}\left(\operatorname{functionalInput}\left(I, s\right), p, w\right))) \iff \exists! v: \operatorname{Fin}\left(m\right) \to CompletionTree, ((\operatorname{OriginalAdmissible}\left(I, p, v\right) \land \operatorname{imageValues}\left(s, v\right) = w))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeComputedEpochPotential.cycleCondition_gives_epoch_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the cycle condition, constructPotential pairs the executable computedPotential tuple with its correctness proof and passes that same tuple directly to the exact epoch correspondence. Literal transformed evaluation, all state-image filters, every additional filter, undefined states and every original reconstruction therefore remain in the same fixed parameter relation. The tuple is independent of the requested prefix depth; this finite construction and solution correspondence do not assert the full effective-prefix and rigidity conclusion.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeComputedEpochPotential.computedPotential`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeComputedEpochPotential.constructPotential`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeComputedEpochPotential.cycleCondition_gives_epoch_transport`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeComputedEpochPotential.cycleCondition_iff_potential`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeOriginalReconstructionBridge](NativeOriginalReconstructionBridge.md)
- Dependency: [D5/S3/Combinatorics/Graph/LayeredCirculation/SupplierDual](../../../../Combinatorics/Graph/LayeredCirculation/SupplierDual.md)

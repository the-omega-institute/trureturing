# Actual phase factors and invariant measures

## Abstract

Invariant probabilities and finite cyclic phases of the actual balanced subshift.

**Definition 1.1 (Physical phase).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedMeasures.phase`

*Formalization.* `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedMeasures.phase` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A point of the compact balanced subshift has a unique marked tiling at every level. Its phase is the offset at zero, regarded as a residue modulo the common word height. Continuity follows from continuity of the actual decoder and the discrete tile-state space. Translation by any signed integer adds that integer to the phase.

**Theorem 1.2 (Existence of an invariant probability).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedMeasures.exists_balanced_invariant_probability`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedMeasures.exists_balanced_invariant_probability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The shift restricts to a continuous self-map of the nonempty compact Hausdorff balanced subshift. Applying Mathlib's Krylov--Bogolyubov theorem gives a Borel probability preserved by the one-step shift. This is an invariant measure on the actual point space, with no abstract tower or incidence-vector hypothesis.

**Theorem 1.3 (Uniform phase marginal).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedMeasures.phase_fiber_measure`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedMeasures.phase_fiber_measure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any invariant probability, adjacent phase fibres have equal mass because the one-step shift adds one to phase. Every cyclic residue is a nonnegative iterate of zero. The complete finite fibre partition has total mass one, so each fibre has mass 1/h(n). Consequently a finite phase set has its cardinality divided by h(n) as its exact mass.

**Definition 1.4 (Finite-window events).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedMeasures.WindowDetermined`

*Formalization.* `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedMeasures.WindowDetermined` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An event is determined by a signed finite window when any two actual points agreeing throughout that window have the same event membership. This allows arbitrary sets of finite-coordinate assignments, including the empty event, rather than only a single prescribed word.

**Theorem 1.5 (A common counting interval).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedMeasures.window_event_measure_squeeze`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedMeasures.window_event_measure_squeeze` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Declare a phase good when its entire actual fibre belongs to the event. The union of good fibres lies inside the event. Outside the sparse translated disagreement set, any two points with the same phase agree on the entire window, including all seams; hence every event point outside the exceptional phases belongs to a good fibre. Uniform phase mass bounds the event mass between the good-phase fraction and that fraction plus the exceptional-phase fraction, simultaneously for every invariant probability. No representative is selected in any phase fibre.

## References

- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedMeasures.WindowDetermined`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedMeasures.exists_balanced_invariant_probability`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedMeasures.phase`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedMeasures.phase_fiber_measure`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedMeasures.window_event_measure_squeeze`
- Dependency: [D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedSubshift](BalancedSubshift.md)
- Dependency: [D5/S1/Dynamics/Symbolic/PermutativeLifts/SparseDisagreement](SparseDisagreement.md)

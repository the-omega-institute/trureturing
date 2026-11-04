# Möbius orbit counts for cyclic additive skew products

## Abstract

The cyclic fiber multiplicity survives Möbius inversion: exact lifted cycle counts factor through the zero-holonomy return table on the base.

**Theorem 1.1 (Holonomy factorization of the Möbius transform).**

Lean statement: `D5/S1/Dynamics/PeriodicOrbits/SkewZModOrbitCount.delta_fixed_count_skew_zmod`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/PeriodicOrbits/SkewZModOrbitCount.delta_fixed_count_skew_zmod` (`✓ std3`). ∎

**Theorem 1.2 (Weighted exact-cycle factorization).**

Lean statement: `D5/S1/Dynamics/PeriodicOrbits/SkewZModOrbitCount.weighted_cycle_count_factorization`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/PeriodicOrbits/SkewZModOrbitCount.weighted_cycle_count_factorization` (`✓ std3`). ∎

**Theorem 1.3 (Divisibility invariant).**

Lean statement: `D5/S1/Dynamics/PeriodicOrbits/SkewZModOrbitCount.zmod_dvd_weighted_cycle_count`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/PeriodicOrbits/SkewZModOrbitCount.zmod_dvd_weighted_cycle_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a skew product with fiber `ZMod q`, every zero-holonomy base return lifts to all `q` phases. The fixed-point table is therefore `q` times the base zero-holonomy table. The Möbius transform is linear, so the same factor survives when fixed points are converted into exact cycle counts.

The resulting identity says that `(n : ℤ) * cycleLengthMultiplicity` is `q` times an explicitly computable base transform. This is an arithmetic shadow of the cyclic group action: even when individual cycles have different lengths because of holonomy orders, the weighted primitive-cycle count retains the full fiber cardinality as a divisibility invariant.

*Dependency.* [SkewZModFixedCount](SkewZModFixedCount.md)

## References

- Truth anchor: `D5/S1/Dynamics/PeriodicOrbits/SkewZModOrbitCount.delta_fixed_count_skew_zmod`
- Truth anchor: `D5/S1/Dynamics/PeriodicOrbits/SkewZModOrbitCount.weighted_cycle_count_factorization`
- Truth anchor: `D5/S1/Dynamics/PeriodicOrbits/SkewZModOrbitCount.zmod_dvd_weighted_cycle_count`
- Dependency: [SkewZModFixedCount](SkewZModFixedCount.md)
- Dependency: [OrbitCounting](OrbitCounting.md)

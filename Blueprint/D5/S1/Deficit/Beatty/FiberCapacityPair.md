# Capacity Pairs and Interval Support of Golden Fibers

## Abstract

Positive golden first-coordinate fibers have capacity four or five, nonnegative dual fibers have capacity two or three, and each first-coordinate fiber has interval support in the second coordinate.

**Lemma 1.1 (Positive golden fibers are finite).**

$$\forall a \in \mathbb{Z}, 1 \leq a \Rightarrow \operatorname{Finite}(\operatorname{goldenFiber}(a))$$

*Proof.* Machine-checked in Lean as `D5/S1/Deficit/Beatty/FiberCapacityPair.golden_fiber_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fixing a positive first coordinate leaves only finitely many word indices. Their second coordinates lie between two finite golden-ratio floor cutoffs, and each supported coordinate reconstructs one index.

**Theorem 1.2 (Positive golden fibers have capacity four or five).**

$$\forall a \in \mathbb{Z}, 1 \leq a \Rightarrow \operatorname{ncard}(\operatorname{goldenFiber}(a)) \in \{ 4, 5 \}$$

*Proof.* Machine-checked in Lean as `D5/S1/Deficit/Beatty/FiberCapacityPair.golden_fiber_capacity_pair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive integer first-coordinate label, the corresponding golden fiber contains exactly four or exactly five indices.

The two floor cutoffs for its second-coordinate support differ by three or four. Counting both endpoints of that integer interval gives the two possible fiber capacities.

**Lemma 1.3 (Nonnegative dual fibers have capacity two or three).**

$$\forall b \in \mathbb{Z}, 0 \leq b \Rightarrow \operatorname{ncard}(\operatorname{goldenDualFiber}(b)) \in \{ 2, 3 \}$$

*Proof.* Machine-checked in Lean as `D5/S1/Deficit/Beatty/FiberCapacityPair.golden_dual_fiber_capacity_pair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every nonnegative integer second-coordinate label, fixing that coordinate selects exactly two or exactly three natural indices.

Successive ceiling cutoffs at the golden-ratio-square scale differ by two or three. The zero label is included and has capacity two.

**Lemma 1.4 (Second-coordinate support is a closed integer interval).**

$$\forall a \in \mathbb{Z}, 1 \leq a \Rightarrow \operatorname{fiberB}[\operatorname{goldenFiber}(a)] = \{ b \in \mathbb{Z} | \operatorname{fiberSupportLower}(a) \leq b \land b \leq \operatorname{fiberSupportUpper}(a) \}$$

*Proof.* Machine-checked in Lean as `D5/S1/Deficit/Beatty/FiberCapacityPair.golden_fiber_b_support_eq_Icc` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a positive first-coordinate label a, the second coordinates attained in its fiber are precisely all integers from floor((a - 1) phi) through floor((a + 1) phi), with both endpoints included.

Every index in the fiber lands in this interval, and reconstructing an index from any integer in the interval realizes the reverse inclusion.

**Lemma 1.5 (Second-coordinate support is order connected).**

$$\forall a \in \mathbb{Z}, 1 \leq a \Rightarrow \operatorname{OrdConnected}(\operatorname{fiberB}[\operatorname{goldenFiber}(a)])$$

*Proof.* Machine-checked in Lean as `D5/S1/Deficit/Beatty/FiberCapacityPair.golden_fiber_b_support_ordConnected` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Within a positive first-coordinate fiber, every integer lying between two attained second coordinates is also attained. This follows from the exact identification of the support with a closed integer interval.

## References

- Truth anchor: `D5/S1/Deficit/Beatty/FiberCapacityPair.golden_dual_fiber_capacity_pair`
- Truth anchor: `D5/S1/Deficit/Beatty/FiberCapacityPair.golden_fiber_b_support_eq_Icc`
- Truth anchor: `D5/S1/Deficit/Beatty/FiberCapacityPair.golden_fiber_b_support_ordConnected`
- Truth anchor: `D5/S1/Deficit/Beatty/FiberCapacityPair.golden_fiber_capacity_pair`
- Truth anchor: `D5/S1/Deficit/Beatty/FiberCapacityPair.golden_fiber_finite`
- Dependency: [D5/S1/Deficit/Beatty/FiberCoordinateBeattyForms](FiberCoordinateBeattyForms.md)
- Dependency: [D5/S1/Depth/GoldenPowerRounding](../../Depth/GoldenPowerRounding.md)

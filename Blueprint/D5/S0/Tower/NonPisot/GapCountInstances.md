# Further Non-Pisot Gap Count Instances

## Abstract

Three further finite beta13 gap counts are certified, and the frozen ten-digit model is proved inadequate for an all-level theorem.

These are individual finite computations at levels three, four, and five. They add evidence but do not state or prove a growth law.

**Theorem 1.1 (Three normalized gap types at level three).**

$$\operatorname{card}\left(\operatorname{beta13NormalizedGapSpectrum}\left(3\right)\right) = 3$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/NonPisot/GapCountInstances.beta13_normalized_gap_type_count_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite internal adjacent-gap spectrum at Q = 3 has cardinality three.

**Theorem 1.2 (Four normalized gap types at level four).**

$$\operatorname{card}\left(\operatorname{beta13NormalizedGapSpectrum}\left(4\right)\right) = 4$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/NonPisot/GapCountInstances.beta13_normalized_gap_type_count_four` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite internal adjacent-gap spectrum at Q = 4 has cardinality four.

**Theorem 1.3 (Five normalized gap types at level five).**

$$\operatorname{card}\left(\operatorname{beta13NormalizedGapSpectrum}\left(5\right)\right) = 5$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/NonPisot/GapCountInstances.beta13_normalized_gap_type_count_five` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite internal adjacent-gap spectrum at Q = 5 has cardinality five.

**Theorem 1.4 (The frozen prefix model stops before the actual eleventh digit).**

$$\operatorname{getOptional}\left(\mathit{beta13RemainderCodes}, 10\right) = \operatorname{some}\left(\operatorname{pair}\left(21, 0 - 9\right)\right) \land \left(\operatorname{floor}\left(\mathit{beta13} \cdot \operatorname{beta13GapCodeValue}\left(\operatorname{pair}\left(21, 0 - 9\right)\right)\right) = 0 \land \left(\operatorname{beta13BelowGreedyPrefix}\left(\operatorname{append}\left(\mathit{beta13GreedyDigits}, \operatorname{singleton}\left(0\right)\right)\right) = \mathit{false} \land \left(\neg \operatorname{append}\left(\mathit{beta13GreedyDigits}, \operatorname{singleton}\left(0\right)\right) \in \operatorname{beta13Names}\left(11\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/NonPisot/GapCountInstances.beta13_frozen_prefix_rejects_actual_eleven_digit_prefix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact remainder code after ten digits is (21,-9). Its next greedy digit is zero, but appending that digit to the frozen ten-digit list makes the current prefix predicate return false, so the current name generator omits the genuine eleven-digit prefix.

Consequently the imported spectrum is a certified finite-prefix model, not a definition of the greedy beta-shift at arbitrary Q. An all-Q count theorem first requires an infinite greedy digit stream and a proof that its ordered adjacent-gap recursion adds exactly one new remainder type per level.

## References

- Truth anchor: `D5/S0/Tower/NonPisot/GapCountInstances.beta13_frozen_prefix_rejects_actual_eleven_digit_prefix`
- Truth anchor: `D5/S0/Tower/NonPisot/GapCountInstances.beta13_normalized_gap_type_count_five`
- Truth anchor: `D5/S0/Tower/NonPisot/GapCountInstances.beta13_normalized_gap_type_count_four`
- Truth anchor: `D5/S0/Tower/NonPisot/GapCountInstances.beta13_normalized_gap_type_count_three`
- Dependency: [D5/S0/Tower/NonPisot/GapCounts](GapCounts.md)

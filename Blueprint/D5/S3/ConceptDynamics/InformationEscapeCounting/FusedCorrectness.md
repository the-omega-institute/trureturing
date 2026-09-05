# Fused Counting Correctness

## Abstract

The fused catalog census agrees with every frozen reference field.

**Theorem 1.1 (Saturated pair classification).**

$$\operatorname{pairScan}(C, E, x, y) = none \Leftrightarrow \operatorname{indistinguishable}(C, \operatorname{fullIndexSet}(C), x, y)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeCounting/FusedCorrectness.fusedPairClassification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Content. The live escape witness is the singleton scan theorem, which identifies the sole disagreement and proves all other indices agree.

**Theorem 1.2 (Fused full count is exact).**

$$\operatorname{full}(\operatorname{fusedCounts}(C, S, E)) = \operatorname{escapeNumerator}(C, \operatorname{fullIndexSet}(C))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeCounting/FusedCorrectness.fusedFull_eq_escapeNumerator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Content. The live fusedCounts_value fold invariant counts each pair class once; the pair classifier then identifies the matching frozen finset.

**Theorem 1.3 (Every fused unique count is exact).**

$$\operatorname{unique}(\operatorname{fusedCounts}(C, S, E), i) = \operatorname{uniqueCaptureCount}(C, i)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeCounting/FusedCorrectness.fusedUnique_eq_uniqueCaptureCount` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Content. The live fusedCounts_value fold invariant counts each pair class once; the pair classifier then identifies the matching frozen finset.

**Theorem 1.4 (Derived leave-one-out count is exact).**

$$\operatorname{without}(\operatorname{fusedCounts}(C, S, E), i) = \operatorname{escapeNumerator}(C, \operatorname{without}(C, i))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeCounting/FusedCorrectness.fusedWithout_eq_escapeNumerator_without` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Bind-only companion. It rewrites full and unique correctness through the frozen leave-one-out addition law.

**Theorem 1.5 (Every fused role bin is exact).**

$$\operatorname{roleBins}(\operatorname{fusedCounts}(C, S, E), i, b) = \operatorname{roleHistogram}(C, i, \operatorname{roleSignatureOfBucket}(b))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeCounting/FusedCorrectness.fusedRoleBins_eq_roleHistogram` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Content. The live fusedCounts_value fold invariant counts each pair class once; the pair classifier then identifies the matching frozen finset.

**Theorem 1.6 (Fused role bins are complete).**

$$\operatorname{sum}(b, \operatorname{roleBins}(\operatorname{fusedCounts}(C, S, E), i, b)) = \operatorname{unique}(\operatorname{fusedCounts}(C, S, E), i)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeCounting/FusedCorrectness.fusedRoleBins_sum_eq_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Content. Pointwise fused correctness stays live, and the new bucket-signature bijection transports the frozen histogram partition.

**Theorem 1.7 (Fused positivity transports).**

$$0 < \operatorname{unique}(\operatorname{fusedCounts}(C, S, E), i) \Rightarrow 0 < \operatorname{uniqueCaptureCount}(C, i)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeCounting/FusedCorrectness.uniqueCaptureCount_pos_of_fused` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Bind-only companion. It rewrites by fused unique-count correctness.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeCounting/FusedCorrectness.fusedFull_eq_escapeNumerator`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeCounting/FusedCorrectness.fusedPairClassification`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeCounting/FusedCorrectness.fusedRoleBins_eq_roleHistogram`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeCounting/FusedCorrectness.fusedRoleBins_sum_eq_unique`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeCounting/FusedCorrectness.fusedUnique_eq_uniqueCaptureCount`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeCounting/FusedCorrectness.fusedWithout_eq_escapeNumerator_without`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeCounting/FusedCorrectness.uniqueCaptureCount_pos_of_fused`
- Dependency: [D5/S3/ConceptDynamics/InformationEscapeCounting/Fused](Fused.md)

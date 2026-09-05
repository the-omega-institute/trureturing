# Strict Counting Reflection

## Abstract

A strict list fold reflects finite state censuses into the frozen escape-count API.

**Definition 1.1 (Complete state enumeration).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/CountingReflection.StateEnumeration`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/CountingReflection.StateEnumeration` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A duplicate-free state list is certified to contain the whole finite arena.

**Definition 1.2 (Complete index enumeration).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/CountingReflection.IndexEnumeration`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/CountingReflection.IndexEnumeration` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A duplicate-free index list carries pointwise completeness.

**Definition 1.3 (Canonical finite-index enumeration).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/CountingReflection.finIndexEnumeration`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/CountingReflection.finIndexEnumeration` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The ascending finite range enumerates every element of Fin n.

**Definition 1.4 (Strict counting summary).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/CountingReflection.ListUniqueCaptureSummary`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/CountingReflection.ListUniqueCaptureSummary` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Three census totals and fifteen nonzero role-mask buckets form one strict value.

**Definition 1.5 (Summary bucket selector).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/CountingReflection.bucket`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/CountingReflection.bucket` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A zero-based Fin 15 index selects the corresponding nonzero role-mask bucket.

**Definition 1.6 (Bucket role signature).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/CountingReflection.roleSignatureOfBucket`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/CountingReflection.roleSignatureOfBucket` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Bucket bits are decoded high-first in CUT, FLOW, ADMIT, ANCHOR order.

**Definition 1.7 (One-pass reflected census).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscape/CountingReflection.listUniqueCaptureSummary`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscape/CountingReflection.listUniqueCaptureSummary` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A strict nested fold classifies every ordered pair exactly once.

**Theorem 1.8 (Reflected full count is exact).**

$$\operatorname{fullEscapeCount}(\operatorname{listUniqueCaptureSummary}(C, S, E, i)) = \operatorname{escapeNumerator}(C, \operatorname{fullIndexSet}(C))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/CountingReflection.listFullEscapeCount_eq_escapeNumerator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The fold-pair classification invariant transports the list count to the frozen finite census.

**Theorem 1.9 (Reflected leave-one-out count is exact).**

$$\operatorname{withoutEscapeCount}(\operatorname{listUniqueCaptureSummary}(C, S, E, i)) = \operatorname{escapeNumerator}(C, \operatorname{without}(C, i))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/CountingReflection.listWithoutEscapeCount_eq_escapeNumerator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The fold-pair classification invariant transports the list count to the frozen finite census.

**Theorem 1.10 (Reflected unique count is exact).**

$$\operatorname{uniqueCaptureCount}(\operatorname{listUniqueCaptureSummary}(C, S, E, i)) = \operatorname{uniqueCaptureCount}(C, i)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/CountingReflection.listUniqueCaptureCount_eq_uniqueCaptureCount` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The fold-pair classification invariant transports the list count to the frozen finite census.

**Theorem 1.11 (Reflected role buckets are exact).**

$$\operatorname{bucket}(\operatorname{listUniqueCaptureSummary}(C, S, E, i), b) = \operatorname{roleHistogram}(C, i, \operatorname{roleSignatureOfBucket}(b))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/CountingReflection.listBucket_eq_roleHistogram` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The fold-pair classification invariant transports the list count to the frozen finite census.

**Theorem 1.12 (Reflected positivity transports).**

$$0 < \operatorname{uniqueCaptureCount}(\operatorname{listUniqueCaptureSummary}(C, S, E, i)) \Rightarrow 0 < \operatorname{uniqueCaptureCount}(C, i)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscape/CountingReflection.uniqueCaptureCount_pos_of_list` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The fold-pair classification invariant transports the list count to the frozen finite census.

**Example 1.13 (Agenda-power state enumeration).**

$$
stateEnumeration: \operatorname{StateEnumeration}(agendaPowerArena)
$$

*Source.* Repository-derived.

*Commentary.*

FirstThreeArenas.agendaPowerArena.__state_enumeration supplies an explicit duplicate-free complete state list.

**Example 1.14 (Adaptive-residue state enumeration).**

$$
stateEnumeration: \operatorname{StateEnumeration}(residueArena)
$$

*Source.* Repository-derived.

*Commentary.*

FirstThreeArenas.residueArena.__state_enumeration supplies an explicit duplicate-free complete state list.

**Example 1.15 (Spectrum state enumeration).**

$$
stateEnumeration: \operatorname{StateEnumeration}(spectrumArena)
$$

*Source.* Repository-derived.

*Commentary.*

FirstThreeArenas.spectrumArena.__state_enumeration supplies an explicit duplicate-free complete state list.

**Example 1.16 (Interpretation-context state enumeration).**

$$
stateEnumeration: \operatorname{StateEnumeration}(contextArena)
$$

*Source.* Repository-derived.

*Commentary.*

FourthFifthArenas.contextArena.__state_enumeration supplies an explicit duplicate-free complete state list.

**Example 1.17 (Intervention state enumeration).**

$$
stateEnumeration: \operatorname{StateEnumeration}(interventionArena)
$$

*Source.* Repository-derived.

*Commentary.*

FourthFifthArenas.interventionArena.__state_enumeration supplies an explicit duplicate-free complete state list.

**Example 1.18 (Observation-intervention state enumeration).**

$$
stateEnumeration: \operatorname{StateEnumeration}(observationInterventionArena)
$$

*Source.* Repository-derived.

*Commentary.*

ObservationIntervention.observationInterventionArena.__state_enumeration supplies an explicit duplicate-free complete state list.

**Example 1.19 (Static-experiment state enumeration).**

$$
stateEnumeration: \operatorname{StateEnumeration}(staticExactExperimentArena)
$$

*Source.* Repository-derived.

*Commentary.*

StaticExactExperimentDesign.staticExactExperimentArena.__state_enumeration supplies an explicit duplicate-free complete state list.

**Example 1.20 (Commuting-completion state enumeration).**

$$
stateEnumeration: \operatorname{StateEnumeration}(commutingCompletionArena)
$$

*Source.* Repository-derived.

*Commentary.*

CommutingCompletionExchange.commutingCompletionArena.__state_enumeration supplies an explicit duplicate-free complete state list.

**Example 1.21 (Local-law-gluing state enumeration).**

$$
stateEnumeration: \operatorname{StateEnumeration}(localLawGluingArena)
$$

*Source.* Repository-derived.

*Commentary.*

LocalLawGluingObstruction.localLawGluingArena.__state_enumeration supplies an explicit duplicate-free complete state list.

**Example 1.22 (Preemption-trace state enumeration).**

$$
stateEnumeration: \operatorname{StateEnumeration}(endStateOmitsPreemptingCauseArena)
$$

*Source.* Repository-derived.

*Commentary.*

EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena.__state_enumeration supplies an explicit duplicate-free complete state list.

**Example 1.23 (SYSTEM stage enumeration).**

$$
stateEnumeration: \operatorname{StateEnumeration}(arena)
$$

*Source.* Repository-derived.

*Commentary.*

SystemUnit.arena.__state_enumeration supplies an explicit duplicate-free complete state list.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/CountingReflection.IndexEnumeration`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/CountingReflection.ListUniqueCaptureSummary`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/CountingReflection.StateEnumeration`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/CountingReflection.bucket`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/CountingReflection.finIndexEnumeration`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/CountingReflection.listBucket_eq_roleHistogram`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/CountingReflection.listFullEscapeCount_eq_escapeNumerator`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/CountingReflection.listUniqueCaptureCount_eq_uniqueCaptureCount`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/CountingReflection.listUniqueCaptureSummary`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/CountingReflection.listWithoutEscapeCount_eq_escapeNumerator`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/CountingReflection.roleSignatureOfBucket`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscape/CountingReflection.uniqueCaptureCount_pos_of_list`
- Dependency: [D5/S3/ConceptDynamics/InformationEscape/RoleHistogram](RoleHistogram.md)
- Dependency: [D5/S3/ConceptDynamics/InformationEscape/SystemUnit](SystemUnit.md)
- Dependency: [D5/S3/ConceptDynamics/InformationEscapeRealizations/CommutingCompletionExchange](../InformationEscapeRealizations/CommutingCompletionExchange.md)
- Dependency: [D5/S3/ConceptDynamics/InformationEscapeRealizations/EndStateOmitsPreemptingCause](../InformationEscapeRealizations/EndStateOmitsPreemptingCause.md)
- Dependency: [D5/S3/ConceptDynamics/InformationEscapeRealizations/FirstThreeRealizations](../InformationEscapeRealizations/FirstThreeRealizations.md)
- Dependency: [D5/S3/ConceptDynamics/InformationEscapeRealizations/FourthFifthRealizations](../InformationEscapeRealizations/FourthFifthRealizations.md)
- Dependency: [D5/S3/ConceptDynamics/InformationEscapeRealizations/LocalLawGluingObstruction](../InformationEscapeRealizations/LocalLawGluingObstruction.md)
- Dependency: [D5/S3/ConceptDynamics/InformationEscapeRealizations/ObservationIntervention](../InformationEscapeRealizations/ObservationIntervention.md)
- Dependency: [D5/S3/ConceptDynamics/InformationEscapeRealizations/StaticExactExperimentDesign](../InformationEscapeRealizations/StaticExactExperimentDesign.md)

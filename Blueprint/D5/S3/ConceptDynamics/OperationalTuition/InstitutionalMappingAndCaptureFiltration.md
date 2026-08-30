# Institutional Mapping and Capture Filtration

## Abstract

Append-only institution registration and T1-compliant event classification make operational tuition monotone, decidable, and locally auditable.

**Theorem 1.1 (Institution domains grow and defects are decidable).**

$$\forall C, I: Type, [\operatorname{DecidableEq}\left(C\right)],\\{}(\forall tau, upsilon: \operatorname{OperationalTrajectory}\left(C, I\right), \operatorname{IsTrajectoryPrefix}\left(tau, upsilon\right) \Rightarrow \operatorname{institutionDomain}\left(tau\right) \subseteq \operatorname{institutionDomain}\left(upsilon\right)) \land\\{}(\forall h: \operatorname{List}\left(\operatorname{Event}\left(C\right)\right), e: \operatorname{Event}\left(C\right), \operatorname{defectDecision}\left(h, e\right) = true \iff \operatorname{InstitutionalDefect}\left(h, e\right)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/OperationalTuition/InstitutionalMappingAndCaptureFiltration.institution_domain_monotone_and_defect_decidable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An operational trajectory is a finite event list. A registration event adds its error class to the defined domain of the partial institution map, and list extension never removes that witness.

The second conjunct is computational: defectDecision returns true exactly when the class occurred earlier and its institution was already registered. Thus the same-class recurrence violation is decidable without a private axiom.

**Theorem 1.2 (Capture levels filter and decreases locate defects).**

$$\forall C, I: Type, [\operatorname{DecidableEq}\left(C\right)],\\{}tau: \operatorname{T1CompliantTrajectory}\left(C, I\right),\\{}\operatorname{Monotone}\left(\operatorname{captureFiltration}\left(tau\right)\right) \land\\{}(\forall h, m, s: \operatorname{List}\left(\operatorname{Event}\left(C\right)\right), e0, e1: \operatorname{Event}\left(C\right),\\{}(\operatorname{events}\left(tau\right) = \operatorname{append}\left(h, \operatorname{append}\left([e0], \operatorname{append}\left(m, \operatorname{append}\left([e1], s\right)\right)\right)\right) \land \operatorname{institutionEstablished}\left(h, \operatorname{errorClass}\left(e0\right)\right) = true \land \operatorname{errorClass}\left(e0\right) = \operatorname{errorClass}\left(e1\right)) \Rightarrow\\{}\operatorname{capture}\left(e0\right) \leq \operatorname{capture}\left(e1\right) \lor \operatorname{LocatedInstitutionalDefect}\left(tau, e1\right)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/OperationalTuition/InstitutionalMappingAndCaptureFiltration.capture_ladder_filtration_and_t1_nondecreasing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The threshold event sets are monotone from wall through gate to author: raising the threshold retains every event already admitted.

For two occurrences of an already institutionalized class, either the later capture level is no lower or T1 marks that later occurrence as an institutional defect. The located-defect conclusion carries the exact prefix and suffix around the exceptional event.

The T1 law is evidence stored in T1CompliantTrajectory, not a Lean axiom. A compiled finite witness realizes the exception branch with a gate-to-wall decrease.

## References

- Truth anchor: `D5/S3/ConceptDynamics/OperationalTuition/InstitutionalMappingAndCaptureFiltration.capture_ladder_filtration_and_t1_nondecreasing`
- Truth anchor: `D5/S3/ConceptDynamics/OperationalTuition/InstitutionalMappingAndCaptureFiltration.institution_domain_monotone_and_defect_decidable`

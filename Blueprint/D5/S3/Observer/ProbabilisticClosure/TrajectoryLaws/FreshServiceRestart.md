# Repeated acceptance on one fresh stream

## Abstract

FreshServiceRestart

An iid external stream supplies candidates one at a time. The first accepted coordinate and the suffix strictly after it are semantic execution coordinates. Neither the search index nor the suffix is a retained machine register or a readable random tape. The fallback totalizes the zero-mass event of never accepting.

A first-hit event fixes a rejected prefix and one accepted candidate. Independence of disjoint coordinate sets factors its joint mass with any measurable suffix event. The rejected-prefix masses form a geometric series. Positive acceptance mass makes infinite rejection null, and summing the disjoint first-hit events gives the conditional accepted law times the unchanged iid suffix law.

Repeated services always consume the unused suffix of that same stream. Their prefix probabilities follow by induction from the joint restart identity. Equality of every finite prefix, followed by projective-limit uniqueness, identifies the complete infinite output measure. Countable intersection of the full-measure return events covers every repeated service.

RarePriorSerialExecution.repeated_fresh_bit_service applies this result to consecutive packets of seven external fair bits and relates the accepted candidates to the existing reset/bit/compare trajectory. This probability theorem does not implement a scanner or renderer, charge a complete machine snapshot, establish original COMPLETE membership or optimize an original inf-sup risk.

**Theorem 1.1 (First hit characterization).**

$$\forall (\operatorname{A} : \operatorname{Type}) , \forall (\operatorname{inst} : \operatorname{MeasurableSpace} (\operatorname{A})) , \forall (\operatorname{accept} : \operatorname{Set} (\operatorname{A})) , \forall (\operatorname{omega} : \mathbb{N} \to \operatorname{A}) , \forall (\operatorname{n} : \mathbb{N}) , \operatorname{firstHit} (\operatorname{accept} , \operatorname{omega}) = \operatorname{some} (\operatorname{n}) \iff \operatorname{omega} (\operatorname{n}) \in \operatorname{accept} \land \forall \operatorname{i} < \operatorname{n} , \neg (\operatorname{omega} (\operatorname{i}) \in \operatorname{accept})$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FreshServiceRestart.first_hit_some` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The selected index has an accepted candidate and every strictly earlier coordinate rejects.

**Theorem 1.2 (Accepted value and untouched suffix).**

$$\forall (\operatorname{A} : \operatorname{Type}) , \forall (\operatorname{inst} : \operatorname{MeasurableSpace} (\operatorname{A})) , \forall (\operatorname{mu} : \operatorname{Measure} (\operatorname{A})) , \forall (\operatorname{hprob} : \operatorname{IsProbabilityMeasure} (\operatorname{mu})) , \forall (\operatorname{accept} : \operatorname{Set} (\operatorname{A})) , \forall (\operatorname{fallback} : \operatorname{A}) , \operatorname{MeasurableSet} (\operatorname{accept}) \to \operatorname{mu} (\operatorname{accept}) \neq 0 \to \operatorname{Measure}.\operatorname{map} (\operatorname{restart} (\operatorname{accept} , \operatorname{fallback}) , \operatorname{Measure}.\operatorname{infinitePi} (\operatorname{fun} \operatorname{i} : \mathbb{N} \mapsto \operatorname{mu})) = \operatorname{Measure}.\operatorname{prod} (\operatorname{ProbabilityTheory}.\operatorname{cond} (\operatorname{mu} , \operatorname{accept}) , \operatorname{Measure}.\operatorname{infinitePi} (\operatorname{fun} \operatorname{i} : \mathbb{N} \mapsto \operatorname{mu}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FreshServiceRestart.first_acceptance_restart` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

First acceptance yields the conditional accepted value independently of the entire unused iid suffix.

**Theorem 1.3 (Whole repeated output law).**

$$\forall (\operatorname{A} : \operatorname{Type}) , \forall (\operatorname{inst} : \operatorname{MeasurableSpace} (\operatorname{A})) , \forall (\operatorname{finite} : \operatorname{Fintype} (\operatorname{A})) , \forall (\operatorname{singletons} : \operatorname{MeasurableSingletonClass} (\operatorname{A})) , \forall (\operatorname{mu} : \operatorname{Measure} (\operatorname{A})) , \forall (\operatorname{hprob} : \operatorname{IsProbabilityMeasure} (\operatorname{mu})) , \forall (\operatorname{accept} : \operatorname{Set} (\operatorname{A})) , \forall (\operatorname{fallback} : \operatorname{A}) , \operatorname{MeasurableSet} (\operatorname{accept}) \to \operatorname{mu} (\operatorname{accept}) \neq 0 \to \operatorname{Measurable} (\operatorname{draws} (\operatorname{accept} , \operatorname{fallback})) \land \operatorname{Measure}.\operatorname{map} (\operatorname{draws} (\operatorname{accept} , \operatorname{fallback}) , \operatorname{Measure}.\operatorname{infinitePi} (\operatorname{fun} \operatorname{i} : \mathbb{N} \mapsto \operatorname{mu})) = \operatorname{Measure}.\operatorname{infinitePi} (\operatorname{fun} \operatorname{i} : \mathbb{N} \mapsto \operatorname{ProbabilityTheory}.\operatorname{cond} (\operatorname{mu} , \operatorname{accept})) \land (\operatorname{ae} \operatorname{omega} \operatorname{under} \operatorname{Measure}.\operatorname{infinitePi} (\operatorname{fun} \operatorname{i} : \mathbb{N} \mapsto \operatorname{mu}) , \forall (\operatorname{n} : \mathbb{N}) , \operatorname{firstHit} (\operatorname{accept} , \operatorname{unused} (\operatorname{accept} , \operatorname{fallback} , \operatorname{n} , \operatorname{omega})) \neq \operatorname{none})$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FreshServiceRestart.repeated_acceptance_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complete repeated accepted sequence has the iid conditional-acceptance law, and every repeated service returns outside one null event.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FreshServiceRestart.first_acceptance_restart`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FreshServiceRestart.first_hit_some`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FreshServiceRestart.repeated_acceptance_law`

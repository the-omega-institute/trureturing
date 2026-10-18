# Exact normalization of capped semantic read rules

## Abstract

Exact normalization of capped semantic read rules

A source is a phase phi and a two-sided Boolean spin sequence S. At the active integer address 2e+phi, the visible reply is the XOR of S(e) and S(e+1); separator replies are zero. The hidden value uses the original integer endpoint, including the negative seam. RawRule.next depends only on the unchanged seed and the ordered acquired record. Finite nonnegative waits are separate from a terminal nonreturn.

ReadTree has integer-labelled binary read nodes and leaves labelled by an optional hidden output. Execution retains the complete ordered address/reply record. paid is its length, so repeated and separator calls remain charged. A none leaf records nonreturn at its exact depth. TotalCap bounds the uncapped extended-natural paidCount on every phase, spin sequence and seed, including exceptional paths.

**Theorem 1.1 (Exact suffix execution).**

$$\forall (\operatorname{U} : \operatorname{Type}), ([\operatorname{MeasurableSpace} (\operatorname{U})] \forall (\operatorname{Q} : \operatorname{RawRule} (\operatorname{U})), (\forall (\operatorname{u} : \operatorname{U}), (\forall (\operatorname{x} : (\operatorname{Int} \to \operatorname{Bool})), (\forall (\operatorname{k} : \operatorname{Nat}), (\forall (\operatorname{n} : \operatorname{Nat}), (\forall (\operatorname{r} : \operatorname{Record}), (((\operatorname{readPrefix} (\operatorname{Q}, \operatorname{u}, \operatorname{x}, \operatorname{n}) = \operatorname{some} (\operatorname{r})) \land (\forall (\operatorname{m} : \operatorname{Nat}), (\forall (\operatorname{s} : \operatorname{Record}), ((\operatorname{readPrefix} (\operatorname{Q}, \operatorname{u}, \operatorname{x}, \operatorname{m}) = \operatorname{some} (\operatorname{s})) \to (\operatorname{m} \le (\operatorname{n} + \operatorname{k})))))) \to (\operatorname{let} \operatorname{v} := \operatorname{run} (\operatorname{unfold} (\operatorname{Q}, \operatorname{k}, \operatorname{u}, \operatorname{r}), \operatorname{x}) \operatorname{in} ((\operatorname{readPrefix} (\operatorname{Q}, \operatorname{u}, \operatorname{x}, (\operatorname{n} + \operatorname{paid} (\operatorname{v}))) = \operatorname{some} (\operatorname{append} (\operatorname{r}, \operatorname{record} (\operatorname{v})))) \land (\operatorname{next} (\operatorname{Q}, \operatorname{u}, \operatorname{append} (\operatorname{r}, \operatorname{record} (\operatorname{v}))) = \operatorname{terminal} (\operatorname{output} (\operatorname{v}))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/SemanticNormalization.unfold_correct` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Starting at any acquired record with at most k further calls, unfolding reaches the original terminal event with precisely the appended execution record. The induction is on the remaining call budget; a further read at budget zero contradicts the cap.

**Theorem 1.2 (Pointwise preservation on every actual capped path).**

$$\forall (\operatorname{U} : \operatorname{Type}), ([\operatorname{MeasurableSpace} (\operatorname{U})] \forall (\operatorname{Q} : \operatorname{RawRule} (\operatorname{U})), (\forall (\operatorname{k} : \operatorname{Nat}), ((\operatorname{TotalCap} (\operatorname{Q}, \operatorname{k})) \to (\forall (\operatorname{phi} : \operatorname{Bool}), (\forall (\operatorname{S} : \operatorname{Spins}), (\forall (\operatorname{u} : \operatorname{U}), ((\operatorname{Completes} (\operatorname{Q}, \operatorname{u}, \operatorname{visible} (\operatorname{phi}, \operatorname{S}), \operatorname{run} (\operatorname{normalize} (\operatorname{Q}, \operatorname{k}, \operatorname{u}), \operatorname{visible} (\operatorname{phi}, \operatorname{S})))) \land (\operatorname{output} (\operatorname{Q}, \operatorname{u}, \operatorname{visible} (\operatorname{phi}, \operatorname{S})) = \operatorname{output} (\operatorname{run} (\operatorname{normalize} (\operatorname{Q}, \operatorname{k}, \operatorname{u}), \operatorname{visible} (\operatorname{phi}, \operatorname{S})))) \land (\operatorname{paidCount} (\operatorname{Q}, \operatorname{u}, \operatorname{visible} (\operatorname{phi}, \operatorname{S})) = \operatorname{paid} (\operatorname{run} (\operatorname{normalize} (\operatorname{Q}, \operatorname{k}, \operatorname{u}), \operatorname{visible} (\operatorname{phi}, \operatorname{S})))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/SemanticNormalization.normalization_pointwise` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

normalize unfolds from the empty record. Completes identifies its exact original terminal record, output and paid count. Return/nonreturn indicators agree as well: a finite number of finite waits remains finite. The height bound applies to every formal branch, with no padding of earlier terminals.

**Theorem 1.3 (Measurable ordinary tree selector).**

$$\forall (\operatorname{U} : \operatorname{Type}), ([\operatorname{MeasurableSpace} (\operatorname{U})] \forall (\operatorname{Q} : \operatorname{RawRule} (\operatorname{U})), (\forall (\operatorname{k} : \operatorname{Nat}), ((\operatorname{Lawful} (\operatorname{Q})) \to (\operatorname{Measurable} (\operatorname{normalize} (\operatorname{Q}, \operatorname{k}))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/SemanticNormalization.measurable_normalize` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite tree type is countable and carries its discrete measurable structure. Measurability follows by induction through next-event decisions at countably many records.

**Theorem 1.4 (One common ordinary version for seed completion).**

$$\forall (\operatorname{U} : \operatorname{Type}), ([\operatorname{MeasurableSpace} (\operatorname{U})] \forall (\operatorname{Q} : \operatorname{RawRule} (\operatorname{U})), (\forall (\operatorname{nu} : \operatorname{Measure} (\operatorname{U})), (\forall (\operatorname{k} : \operatorname{Nat}), (((\operatorname{CompletionLawful} (\operatorname{Q}, \operatorname{nu})) \land (\operatorname{TotalCap} (\operatorname{Q}, \operatorname{k}))) \to (\exists (\operatorname{T} : (\operatorname{U} \to \operatorname{CappedTrees} (\operatorname{k}))), ((\operatorname{Measurable} (\operatorname{T})) \land (\operatorname{AE} (\operatorname{nu}, \operatorname{fun} \operatorname{u} \mapsto (\operatorname{normalize} (\operatorname{Q}, \operatorname{k}, \operatorname{u}) = \operatorname{val} (\operatorname{apply} (\operatorname{T}, \operatorname{u}))))) \land (\operatorname{AE} (\operatorname{nu}, \operatorname{fun} \operatorname{u} \mapsto (\forall (\operatorname{phi} : \operatorname{Bool}), (\forall (\operatorname{S} : \operatorname{Spins}), ((\operatorname{Completes} (\operatorname{Q}, \operatorname{u}, \operatorname{visible} (\operatorname{phi}, \operatorname{S}), \operatorname{run} (\operatorname{val} (\operatorname{apply} (\operatorname{T}, \operatorname{u})), \operatorname{visible} (\operatorname{phi}, \operatorname{S})))) \land (\operatorname{output} (\operatorname{Q}, \operatorname{u}, \operatorname{visible} (\operatorname{phi}, \operatorname{S})) = \operatorname{output} (\operatorname{run} (\operatorname{val} (\operatorname{apply} (\operatorname{T}, \operatorname{u})), \operatorname{visible} (\operatorname{phi}, \operatorname{S})))) \land (\operatorname{paidCount} (\operatorname{Q}, \operatorname{u}, \operatorname{visible} (\operatorname{phi}, \operatorname{S})) = \operatorname{paid} (\operatorname{run} (\operatorname{val} (\operatorname{apply} (\operatorname{T}, \operatorname{u})), \operatorname{visible} (\operatorname{phi}, \operatorname{S})))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/SemanticNormalization.completion_normalization_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

CappedTrees(k) is the subtype of trees of height at most k. One measurable selector agrees for almost every seed; on that common set it preserves every source execution. This statement does not assert pointwise agreement of arbitrary completed versions at every seed.

**Theorem 1.5 (Exact recovery of a bounded tree family).**

$$\forall (\operatorname{U} : \operatorname{Type}), ([\operatorname{MeasurableSpace} (\operatorname{U})] \forall (\operatorname{T} : (\operatorname{U} \to \operatorname{ReadTree})), (\forall (\operatorname{k} : \operatorname{Nat}), (\forall (\operatorname{u} : \operatorname{U}), ((\operatorname{height} (\operatorname{apply} (\operatorname{T}, \operatorname{u})) \le \operatorname{k}) \to (\operatorname{normalize} (\operatorname{realize} (\operatorname{T}), \operatorname{k}, \operatorname{u}) = \operatorname{apply} (\operatorname{T}, \operatorname{u}))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/SemanticNormalization.normalize_realize` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

realize follows the ordered acquired record, rejecting inconsistent addresses. When the supplied tree already has height at most k, normalization recovers it exactly.

**Theorem 1.6 (Ordinary selector for ambient completed events).**

$$\forall (\operatorname{U} : \operatorname{Type}), ([\operatorname{MeasurableSpace} (\operatorname{U})] \forall (\operatorname{Q} : \operatorname{CompletedRule} (\operatorname{U})), (\forall (\operatorname{mu} : \operatorname{Measure} (\operatorname{Prod} (\operatorname{SourcePoint}, \operatorname{U}))), (\forall (\operatorname{k} : \operatorname{Nat}), ((\operatorname{Lawful} (\operatorname{Q}, \operatorname{mu})) \to (\exists (\operatorname{T} : (\operatorname{U} \to \operatorname{CappedTrees} (\operatorname{k}))), ((\operatorname{Measurable} (\operatorname{T})) \land (\operatorname{AE} (\operatorname{mu}, \operatorname{fun} \operatorname{p} \mapsto (\operatorname{normalize} (\operatorname{Q}, \operatorname{k}, \operatorname{p}) = \operatorname{val} (\operatorname{apply} (\operatorname{T}, \operatorname{snd} (\operatorname{p}))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/SemanticNormalization.normalization_version` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

CompletedRule allows source-dependent ambient-null versions of the available observation field. A single ordinary seed selector agrees product-almost everywhere. Separately, completed_normalization_execution preserves each actual completed execution under its all-path cap; that pointwise execution assertion is distinct from the almost-everywhere selector identity.

The normalization construction changes neither the seed space nor the actual read clock. It is a finite semantic unfolding and does not decide divergence of arbitrary programs.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/SemanticNormalization.completion_normalization_bridge`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/SemanticNormalization.measurable_normalize`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/SemanticNormalization.normalization_pointwise`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/SemanticNormalization.normalization_version`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/SemanticNormalization.normalize_realize`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/SemanticNormalization.unfold_correct`

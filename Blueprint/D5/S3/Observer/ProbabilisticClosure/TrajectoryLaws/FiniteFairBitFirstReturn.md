# Sequential fair requests and invocation events

## Abstract

FiniteFairBitFirstReturn

A decoded instruction either performs one deterministic transition or requests one external fair bit. The execution reads the head of the unused iid stream only in the fair case. The stream and its consumed index are probability coordinates; neither is a persistent machine register. Coincident fair successors contribute both half masses to the same state.

The finite prefix proof inducts over physical instructions. A deterministic step keeps the entire unused stream. A fair step uses independence of its head and suffix, proved by the existing FreshServiceRestart first acceptance theorem with the full acceptance set. The two head values give disjoint cylinder events. Their masses add, including when their successors coincide. Only after this operational induction does MarkovPrefixMass identify the cylinders with Kernel.trajMeasure.

**Theorem 1.1 (split_tape).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteFairBitFirstReturn.split_tape`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteFairBitFirstReturn.split_tape` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This existing source lemma is reused directly by the operational certificate.

**Theorem 1.2 (unused_suffix).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteFairBitFirstReturn.unused_suffix`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteFairBitFirstReturn.unused_suffix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This existing source lemma is reused directly by the operational certificate.

**Theorem 1.3 (measurable_run).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteFairBitFirstReturn.measurable_run`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteFairBitFirstReturn.measurable_run` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This existing source lemma is reused directly by the operational certificate.

**Theorem 1.4 (row_fair).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteFairBitFirstReturn.row_fair`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteFairBitFirstReturn.row_fair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This existing source lemma is reused directly by the operational certificate.

**Theorem 1.5 (charged_cardinality).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteFairBitFirstReturn.charged_cardinality`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteFairBitFirstReturn.charged_cardinality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This existing source lemma is reused directly by the operational certificate.

**Theorem 1.6 (Operational finite prefix law).**

$$\forall (\operatorname{S} : \operatorname{Type}) , [\operatorname{Countable} (\operatorname{S})] [\operatorname{MeasurableSpace} (\operatorname{S})] [\operatorname{MeasurableSingletonClass} (\operatorname{S})] \forall (\operatorname{decode} : \operatorname{S} \to \operatorname{Instruction} (\operatorname{S})) , \forall (\operatorname{s} : \operatorname{S}) , \forall (\operatorname{n} : \mathbb{N}) , \forall (\operatorname{w} : \operatorname{Fin} (\operatorname{n} + 1) \to \operatorname{S}) , \operatorname{Measure}.\operatorname{map} (\operatorname{fun} \operatorname{omega} \mapsto \operatorname{fun} (\operatorname{i} : \operatorname{Fin} (\operatorname{n} + 1)) \mapsto \operatorname{run} (\operatorname{decode} , \operatorname{s} , \operatorname{omega} , \operatorname{val} (\operatorname{i})) , \operatorname{tapeLaw}) \{\operatorname{w}\} = \operatorname{Measure}.\operatorname{map} (\operatorname{fun} \operatorname{x} \mapsto \operatorname{fun} (\operatorname{i} : \operatorname{Fin} (\operatorname{n} + 1)) \mapsto \operatorname{x} (\operatorname{val} (\operatorname{i})) , \operatorname{instructionLaw} (\operatorname{decode} , \operatorname{s})) \{\operatorname{w}\}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteFairBitFirstReturn.execution_prefix_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Lean proof establishes exactly this statement under its displayed premises.

The local command syntax contains bit reads and branches, writes, bounded head moves, fair branches, fair bit stores, single symbol buffers, renderer sends, semantic letter emissions and returns. Mode and supplied input are explicit snapshot fields. Arbitrary finite work, persistent phases and computing provider state must occupy charged tape cells. Launch installs its specified entry and input; it does not inspect a previous return. An absent entry gives immediate completion and preserves the remaining snapshot fields.

Return and semantic emission are primitive events, distinct from renderer characters. A semantic letter can be emitted before its bit is erased. The event cut is a coordinate on this same execution, and the bounded executor continues until its first return. It preserves the entire returned snapshot. It introduces no saved semantic letter, accumulated output log or runtime reset.

**Theorem 1.7 (First return and bounded execution).**

$$\forall (\operatorname{p} : \mathbb{N}) , \forall (\operatorname{m} : \mathbb{N}) , \forall (\operatorname{a} : \mathbb{N}) , \forall (\operatorname{P} : \operatorname{Program} (\operatorname{p} , \operatorname{a})) , \forall (\operatorname{s} : \operatorname{Snapshot} (\operatorname{p} , \operatorname{m} , \operatorname{a})) , \forall (\operatorname{mode} : \operatorname{ServiceMode}) , \forall (\operatorname{input} : \operatorname{Option} (\operatorname{Letter})) , \forall (\operatorname{omega} : \mathbb{N} \to \operatorname{Bool}) , \forall (\operatorname{n} : \mathbb{N}) , \forall (\operatorname{t} : \operatorname{Snapshot} (\operatorname{p} , \operatorname{m} , \operatorname{a})) , \operatorname{executeUntil} (\operatorname{P} , \operatorname{launch} (\operatorname{P} , \operatorname{s} , \operatorname{mode} , \operatorname{input}) , \operatorname{omega} , \operatorname{n}) = \operatorname{some} (\operatorname{t}) \iff \exists \operatorname{k} \le \operatorname{n} , \operatorname{firstReturnAt} (\operatorname{P} , \operatorname{launch} (\operatorname{P} , \operatorname{s} , \operatorname{mode} , \operatorname{input}) , \operatorname{omega} , \operatorname{k}) \land \operatorname{snapshot} (\operatorname{fst} (\operatorname{trace} (\operatorname{P} , \operatorname{launch} (\operatorname{P} , \operatorname{s} , \operatorname{mode} , \operatorname{input}) , \operatorname{omega} , \operatorname{k}))) = \operatorname{t}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteFairBitFirstReturn.invocation_return_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Lean proof establishes exactly this statement under its displayed premises.

A complete codec represents the fixed installed program and each admitted micro snapshot in one fixed width binary word. Its round trip is an original representation premise. The micro carrier is the common primitive reachability closure of all supplied entrance snapshots. Induction on physical steps proves that every run from this closure stays in it. The codec yields injectivity and bounds this actual carrier and its ready subset by the number of binary words. The same execution satisfies the request count suffix identity and the physical finite prefix law.

**Theorem 1.8 (Charged primitive execution).**

$$\forall (\operatorname{p} : \mathbb{N}) , \forall (\operatorname{m} : \mathbb{N}) , \forall (\operatorname{a} : \mathbb{N}) , \forall (\operatorname{B} : \mathbb{N}) , \forall (\operatorname{P} : \operatorname{Program} (\operatorname{p} , \operatorname{a})) , \forall (\operatorname{entrances} : \operatorname{Set} (\operatorname{Snapshot} (\operatorname{p} , \operatorname{m} , \operatorname{a}))) , \operatorname{CompleteCodec} (\operatorname{P} , \operatorname{Set}.\operatorname{setOf} (\operatorname{fun} (\operatorname{t} : \operatorname{Snapshot} (\operatorname{p} , \operatorname{m} , \operatorname{a})) \mapsto \operatorname{Reachable} (\operatorname{P} , \operatorname{entrances} , \operatorname{t})) , \operatorname{B}) \to \forall (\operatorname{ready} : \operatorname{Set} (\operatorname{Set}.\operatorname{setOf} (\operatorname{fun} (\operatorname{t} : \operatorname{Snapshot} (\operatorname{p} , \operatorname{m} , \operatorname{a})) \mapsto \operatorname{Reachable} (\operatorname{P} , \operatorname{entrances} , \operatorname{t})))) , [\operatorname{MeasurableSpace} (\operatorname{Snapshot} (\operatorname{p} , \operatorname{m} , \operatorname{a}))] [\operatorname{MeasurableSingletonClass} (\operatorname{Snapshot} (\operatorname{p} , \operatorname{m} , \operatorname{a}))] \forall (\operatorname{s} : \operatorname{Snapshot} (\operatorname{p} , \operatorname{m} , \operatorname{a})) , \operatorname{Reachable} (\operatorname{P} , \operatorname{entrances} , \operatorname{s}) \to \forall (\operatorname{n} : \mathbb{N}) , \forall (\operatorname{w} : \operatorname{Fin} (\operatorname{n} + 1) \to \operatorname{Snapshot} (\operatorname{p} , \operatorname{m} , \operatorname{a})) , \operatorname{Nat}.\operatorname{card} (\operatorname{Set}.\operatorname{setOf} (\operatorname{fun} (\operatorname{t} : \operatorname{Snapshot} (\operatorname{p} , \operatorname{m} , \operatorname{a})) \mapsto \operatorname{Reachable} (\operatorname{P} , \operatorname{entrances} , \operatorname{t}))) \le 2^{\operatorname{B}} \land \operatorname{Nat}.\operatorname{card} (\operatorname{ready}) \le 2^{\operatorname{B}} \land (\forall (\operatorname{omega} : \mathbb{N} \to \operatorname{Bool}) , \operatorname{Reachable} (\operatorname{P} , \operatorname{entrances} , \operatorname{physicalRun} (\operatorname{P} , \operatorname{s} , \operatorname{omega} , \operatorname{n}))) \land (\forall (\operatorname{z} : \operatorname{Snapshot} (\operatorname{p} , \operatorname{m} , \operatorname{a})) , \forall (\operatorname{b} : \operatorname{Bool}) , \operatorname{asks} (\operatorname{code} (\operatorname{P} , \operatorname{pc} (\operatorname{z}))) = \operatorname{false} \to \operatorname{act} (\operatorname{P} , \operatorname{z} , \operatorname{b}) = \operatorname{act} (\operatorname{P} , \operatorname{z} , \operatorname{false})) \land (\forall (\operatorname{omega} : \mathbb{N} \to \operatorname{Bool}) , \forall (\operatorname{k} : \mathbb{N}) , \operatorname{unused} (\operatorname{decoded} (\operatorname{P}) , \operatorname{s} , \operatorname{omega} , \operatorname{n} , \operatorname{k}) = \operatorname{omega} (\operatorname{k} + \operatorname{requests} (\operatorname{decoded} (\operatorname{P}) , \operatorname{s} , \operatorname{omega} , \operatorname{n}))) \land \operatorname{Measure}.\operatorname{map} (\operatorname{fun} \operatorname{omega} \mapsto \operatorname{fun} (\operatorname{i} : \operatorname{Fin} (\operatorname{n} + 1)) \mapsto \operatorname{physicalRun} (\operatorname{P} , \operatorname{s} , \operatorname{omega} , \operatorname{val} (\operatorname{i})) , \operatorname{tapeLaw}) \{\operatorname{w}\} = \operatorname{Measure}.\operatorname{map} (\operatorname{fun} \operatorname{x} \mapsto \operatorname{fun} (\operatorname{i} : \operatorname{Fin} (\operatorname{n} + 1)) \mapsto \operatorname{x} (\operatorname{val} (\operatorname{i})) , \operatorname{instructionLaw} (\operatorname{decoded} (\operatorname{P}) , \operatorname{s})) \{\operatorname{w}\}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteFairBitFirstReturn.charged_execution_prefix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Lean proof establishes exactly this statement under its displayed premises.

The complete codec premise does not prove an implementation of compressed instruction fetching, field decoding or installation temporaries at a given peak. Applying this calculus to the entire charged digital source class still requires a refinement of those paid routines and the original native field layout, preserving primitive events and lawful entrance addresses. Head movement in the local calculus holds at a boundary; applying it to an original program also requires its valid movement boundary. No source prior sampler or receiver archive is encoded by this calculus. Almost sure returns, normalized exit probabilities, reachable state escape, native law correspondence and denominator bounds are separate mathematical obligations.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteFairBitFirstReturn.charged_cardinality`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteFairBitFirstReturn.charged_execution_prefix`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteFairBitFirstReturn.execution_prefix_law`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteFairBitFirstReturn.invocation_return_iff`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteFairBitFirstReturn.measurable_run`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteFairBitFirstReturn.row_fair`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteFairBitFirstReturn.split_tape`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteFairBitFirstReturn.unused_suffix`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FreshServiceRestart](FreshServiceRestart.md)
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/MarkovPrefixMass](MarkovPrefixMass.md)
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeAcquiredPrefixState](NativeAcquiredPrefixState.md)

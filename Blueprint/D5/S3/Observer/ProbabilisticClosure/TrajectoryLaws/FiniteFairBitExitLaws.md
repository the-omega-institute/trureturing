# Actual primitive exit laws and reachable escape

## Abstract

FiniteFairBitExitLaws

An internal state belongs to a finite carrier S. A decoded instruction is deterministic or requests one fresh fair bit. Its successor either remains internal or carries one full exit label in a finite carrier O. The analytical terminal copies are absorbing and consume no further bits. They are proof coordinates; the internal matrix T is indexed only by S. All actual charged runtime state remains in S until the event cut.

A labelled primitive may supply its next physical state together with an optional event. Mapping its result to S plus O gives a cut at that event. The physical edge trace continues after selection. The cut equals the first actual edge observation in the physical prefix, even if a later primitive erases the value. An immediate outcome is an explicit entrance in O. A semantic selection cut and original invocation completion are different events.

**Theorem 1.1 (exits_exit).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteFairBitExitLaws.exits_exit`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteFairBitExitLaws.exits_exit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This existing source lemma is reused directly by the operational certificate.

**Theorem 1.2 (path_exit).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteFairBitExitLaws.path_exit`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteFairBitExitLaws.path_exit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This existing source lemma is reused directly by the operational certificate.

**Theorem 1.3 (step_mass).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteFairBitExitLaws.step_mass`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteFairBitExitLaws.step_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This existing source lemma is reused directly by the operational certificate.

**Theorem 1.4 (exits_partition).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteFairBitExitLaws.exits_partition`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteFairBitExitLaws.exits_partition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This existing source lemma is reused directly by the operational certificate.

**Theorem 1.5 (First actual primitive observation).**

$$\forall (\operatorname{S} : \operatorname{Type}) , \forall (\operatorname{O} : \operatorname{Type}) , [\operatorname{Fintype} (\operatorname{S})] [\operatorname{Fintype} (\operatorname{O})] [\operatorname{MeasurableSpace} (\operatorname{S})] [\operatorname{MeasurableSingletonClass} (\operatorname{S})] [\operatorname{MeasurableSpace} (\operatorname{O})] [\operatorname{MeasurableSingletonClass} (\operatorname{O})] \forall (\operatorname{d} : \operatorname{S} \to \operatorname{Instruction} (\operatorname{Prod} (\operatorname{S} , \operatorname{Option} (\operatorname{O})))) , \forall (\operatorname{s} : \operatorname{S}) , \forall (\operatorname{omega} : \mathbb{N} \to \operatorname{Bool}) , \forall (\operatorname{n} : \mathbb{N}) , \forall (\operatorname{o} : \operatorname{O}) , \operatorname{path} (\operatorname{cut} (\operatorname{d}) , \operatorname{Sum}.\operatorname{inl} (\operatorname{s}) , \operatorname{omega} , \operatorname{n}) = \operatorname{Sum}.\operatorname{inr} (\operatorname{o}) \iff \exists \operatorname{k} < \operatorname{n} , \operatorname{edgeEvent} (\operatorname{d} , \operatorname{s} , \operatorname{omega} , \operatorname{k}) = \operatorname{some} (\operatorname{o}) \land \forall \operatorname{j} < \operatorname{k} , \operatorname{edgeEvent} (\operatorname{d} , \operatorname{s} , \operatorname{omega} , \operatorname{j}) = \operatorname{none}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteFairBitExitLaws.primitive_event_cut` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The statement concerns the displayed finite primitive execution and its actual fair-tape event masses.

Execution reuses the sequential variable-request run and its iid tape measure. Deterministic steps retain the entire suffix; fair steps split the head and unused suffix using FreshServiceRestart. Equality of every finite state prefix with the original instruction trajectory extends to the whole path measure by uniqueness of finite projective limits. Thus the event laws below are laws on the existing Kernel.trajMeasure, rather than a separately assumed Markov process.

First exit at time n means an exit label occurs at n and every earlier analytical state is internal. These events are measurable and pairwise disjoint across both time and complete label. The internal endpoint mass is T to the n-th power. Survival is its row sum, and exit at n plus one has mass T to the n-th power times R. Time zero gives mass one exactly at an immediate exit label. Empty internal carriers and coincident fair successors obey the same formulas.

**Theorem 1.6 (Finite first-exit and survival identities).**

$$\forall (\operatorname{S} : \operatorname{Type}) , \forall (\operatorname{O} : \operatorname{Type}) , [\operatorname{Fintype} (\operatorname{S})] [\operatorname{Fintype} (\operatorname{O})] [\operatorname{MeasurableSpace} (\operatorname{S})] [\operatorname{MeasurableSingletonClass} (\operatorname{S})] [\operatorname{MeasurableSpace} (\operatorname{O})] [\operatorname{MeasurableSingletonClass} (\operatorname{O})] \forall (\operatorname{d} : \operatorname{S} \to \operatorname{Instruction} (\operatorname{Sum} (\operatorname{S} , \operatorname{O}))) , \forall (\operatorname{a} : \operatorname{Sum} (\operatorname{S} , \operatorname{O})) , \operatorname{Measure}.\operatorname{map} (\operatorname{path} (\operatorname{d} , \operatorname{a}) , \operatorname{tapeLaw}) = \operatorname{instructionLaw} (\operatorname{stopped} (\operatorname{d}) , \operatorname{a}) \land (\forall (\operatorname{n} : \mathbb{N}) , \forall (\operatorname{o} : \operatorname{O}) , \operatorname{MeasurableSet} (\operatorname{trajectoryHit} (\operatorname{n} , \operatorname{o})) \land \operatorname{instructionLaw} (\operatorname{stopped} (\operatorname{d}) , \operatorname{a}) (\operatorname{trajectoryHit} (\operatorname{n} , \operatorname{o})) = \operatorname{tapeLaw} (\operatorname{hit} (\operatorname{d} , \operatorname{a} , \operatorname{n} , \operatorname{o}))) \land (\forall (\operatorname{n} : \mathbb{N}) , \forall (\operatorname{o} : \operatorname{O}) , \operatorname{MeasurableSet} (\operatorname{hit} (\operatorname{d} , \operatorname{a} , \operatorname{n} , \operatorname{o}))) \land (\forall (\operatorname{i} : \operatorname{Prod} (\mathbb{N} , \operatorname{O})) , \forall (\operatorname{j} : \operatorname{Prod} (\mathbb{N} , \operatorname{O})) , \operatorname{i} \ne \operatorname{j} \to \operatorname{Disjoint} (\operatorname{hit} (\operatorname{d} , \operatorname{a} , \operatorname{fst} (\operatorname{i}) , \operatorname{snd} (\operatorname{i})) , \operatorname{hit} (\operatorname{d} , \operatorname{a} , \operatorname{fst} (\operatorname{j}) , \operatorname{snd} (\operatorname{j})))) \land (\forall (\operatorname{s} : \operatorname{S}) , \forall (\operatorname{t} : \operatorname{S}) , \forall (\operatorname{n} : \mathbb{N}) , \operatorname{tapeLaw} (\operatorname{Set}.\operatorname{setOf} (\operatorname{fun} \operatorname{omega} \mapsto \operatorname{path} (\operatorname{d} , \operatorname{Sum}.\operatorname{inl} (\operatorname{s}) , \operatorname{omega} , \operatorname{n}) = \operatorname{Sum}.\operatorname{inl} (\operatorname{t}))) = \operatorname{T} (\operatorname{d})^{\operatorname{n}} (\operatorname{s} , \operatorname{t})) \land (\forall (\operatorname{s} : \operatorname{S}) , \forall (\operatorname{n} : \mathbb{N}) , \operatorname{survival} (\operatorname{d} , \operatorname{s} , \operatorname{n}) = \sum_{\operatorname{t}:\operatorname{S}} \operatorname{T} (\operatorname{d})^{\operatorname{n}} (\operatorname{s} , \operatorname{t})) \land (\forall (\operatorname{s} : \operatorname{S}) , \forall (\operatorname{o} : \operatorname{O}) , \forall (\operatorname{n} : \mathbb{N}) , \operatorname{tapeLaw} (\operatorname{hit} (\operatorname{d} , \operatorname{Sum}.\operatorname{inl} (\operatorname{s}) , \operatorname{n}+1 , \operatorname{o})) = (\operatorname{T} (\operatorname{d})^{\operatorname{n}} \times \operatorname{R} (\operatorname{d})) (\operatorname{s} , \operatorname{o})) \land (\forall (\operatorname{o} : \operatorname{O}) , \operatorname{tapeLaw} (\operatorname{hit} (\operatorname{d} , \operatorname{a} , 0 , \operatorname{o})) = \operatorname{if} \operatorname{a} = \operatorname{Sum}.\operatorname{inr} (\operatorname{o}) \operatorname{then} 1 \operatorname{else} 0)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteFairBitExitLaws.finite_exit_laws` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The statement concerns the displayed finite primitive execution and its actual fair-tape event masses.

Reachability starts at every internal permitted entrance in one common graph. An edge is traversable precisely when its actual decoded probability is positive. The nonexit event satisfies the first-step weighted equation. If its mass is zero at one state, every successor of positive weight also has zero nonexit mass. Induction transfers the literal permitted-entry almost-sure exit premise throughout the common reachable graph; a positively reachable trap therefore contradicts that premise.

**Theorem 1.7 (Almost-sure exit on the common reachable graph).**

$$\forall (\operatorname{S} : \operatorname{Type}) , \forall (\operatorname{O} : \operatorname{Type}) , [\operatorname{Fintype} (\operatorname{S})] [\operatorname{Fintype} (\operatorname{O})] [\operatorname{MeasurableSpace} (\operatorname{S})] [\operatorname{MeasurableSingletonClass} (\operatorname{S})] [\operatorname{MeasurableSpace} (\operatorname{O})] [\operatorname{MeasurableSingletonClass} (\operatorname{O})] \forall (\operatorname{d} : \operatorname{S} \to \operatorname{Instruction} (\operatorname{Sum} (\operatorname{S} , \operatorname{O}))) , \forall (\operatorname{E} : \operatorname{Set} (\operatorname{Sum} (\operatorname{S} , \operatorname{O}))) , (\forall \operatorname{a} \in \operatorname{E} , \operatorname{tapeLaw} (\operatorname{never} (\operatorname{d} , \operatorname{a})) = 0) \to \forall (\operatorname{s} : \operatorname{S}) , \operatorname{Reachable} (\operatorname{d} , \operatorname{E} , \operatorname{s}) \to \operatorname{tapeLaw} (\operatorname{never} (\operatorname{d} , \operatorname{Sum}.\operatorname{inl} (\operatorname{s}))) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteFairBitExitLaws.reachable_as_exit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The statement concerns the displayed finite primitive execution and its actual fair-tape event masses.

Survival events decrease to nonexit. Continuity from above makes their masses converge to zero at each reachable state. Finiteness gives one positive length L for which every reachable survival mass is at most one half. Unreachable columns of every power of T are zero for reachable rows. The finite semigroup identity then bounds survival at nL by two to the negative n-th power. Disconnected traps are retained outside this graph; no time cap or irreducibility hypothesis is used.

**Theorem 1.8 (One common positive escape block).**

$$\forall (\operatorname{S} : \operatorname{Type}) , \forall (\operatorname{O} : \operatorname{Type}) , [\operatorname{Fintype} (\operatorname{S})] [\operatorname{Fintype} (\operatorname{O})] [\operatorname{MeasurableSpace} (\operatorname{S})] [\operatorname{MeasurableSingletonClass} (\operatorname{S})] [\operatorname{MeasurableSpace} (\operatorname{O})] [\operatorname{MeasurableSingletonClass} (\operatorname{O})] \forall (\operatorname{d} : \operatorname{S} \to \operatorname{Instruction} (\operatorname{Sum} (\operatorname{S} , \operatorname{O}))) , \forall (\operatorname{E} : \operatorname{Set} (\operatorname{Sum} (\operatorname{S} , \operatorname{O}))) , (\forall \operatorname{a} \in \operatorname{E} , \operatorname{tapeLaw} (\operatorname{never} (\operatorname{d} , \operatorname{a})) = 0) \to \exists \operatorname{L} : \mathbb{N} , 0 < \operatorname{L} \land (\forall (\operatorname{s} : \operatorname{S}) , \operatorname{Reachable} (\operatorname{d} , \operatorname{E} , \operatorname{s}) \to \operatorname{survival} (\operatorname{d} , \operatorname{s} , \operatorname{L}) \le \frac{1}{2}) \land (\forall (\operatorname{s} : \operatorname{S}) , \operatorname{Reachable} (\operatorname{d} , \operatorname{E} , \operatorname{s}) \to \forall (\operatorname{n} : \mathbb{N}) , \operatorname{survival} (\operatorname{d} , \operatorname{s} , \operatorname{n}\times\operatorname{L}) \le \frac{1}{2}^{\operatorname{n}}) \land (\forall (\operatorname{s} : \operatorname{S}) , \operatorname{Reachable} (\operatorname{d} , \operatorname{E} , \operatorname{s}) \to \operatorname{Tendsto} (\operatorname{survival} (\operatorname{d} , \operatorname{s}) , \operatorname{atTop} , \operatorname{nhds} (0))) \land (\forall (\operatorname{s} : \operatorname{S}) , \forall (\operatorname{t} : \operatorname{S}) , \operatorname{Reachable} (\operatorname{d} , \operatorname{E} , \operatorname{s}) \to \operatorname{Not} (\operatorname{Reachable} (\operatorname{d} , \operatorname{E} , \operatorname{t})) \to \forall (\operatorname{n} : \mathbb{N}) , \operatorname{T} (\operatorname{d})^{\operatorname{n}} (\operatorname{s} , \operatorname{t}) = 0)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteFairBitExitLaws.reachable_escape` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The statement concerns the displayed finite primitive execution and its actual fair-tape event masses.

The union of complete first-exit labels is exactly the complement of nonexit. Its disjoint masses add to one at every permitted entrance and every reachable internal state. This normalization is a property of the actual execution events. It is not supplied as an arbitrary probability vector.

**Theorem 1.9 (Actual normalized exit law).**

$$\forall (\operatorname{S} : \operatorname{Type}) , \forall (\operatorname{O} : \operatorname{Type}) , [\operatorname{Fintype} (\operatorname{S})] [\operatorname{Fintype} (\operatorname{O})] [\operatorname{MeasurableSpace} (\operatorname{S})] [\operatorname{MeasurableSingletonClass} (\operatorname{S})] [\operatorname{MeasurableSpace} (\operatorname{O})] [\operatorname{MeasurableSingletonClass} (\operatorname{O})] \forall (\operatorname{d} : \operatorname{S} \to \operatorname{Instruction} (\operatorname{Sum} (\operatorname{S} , \operatorname{O}))) , \forall (\operatorname{E} : \operatorname{Set} (\operatorname{Sum} (\operatorname{S} , \operatorname{O}))) , (\forall \operatorname{a} \in \operatorname{E} , \operatorname{tapeLaw} (\operatorname{never} (\operatorname{d} , \operatorname{a})) = 0) \to (\forall \operatorname{a} \in \operatorname{E} , \sum_{\operatorname{o}:\operatorname{O}} \operatorname{tapeLaw} (\operatorname{exits} (\operatorname{d} , \operatorname{a} , \operatorname{o})) = 1) \land (\forall (\operatorname{s} : \operatorname{S}) , \operatorname{Reachable} (\operatorname{d} , \operatorname{E} , \operatorname{s}) \to \sum_{\operatorname{o}:\operatorname{O}} \operatorname{Z} (\operatorname{d} , \operatorname{s} , \operatorname{o}) = 1)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteFairBitExitLaws.normalized_reachable_exits` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The statement concerns the displayed finite primitive execution and its actual fair-tape event masses.

First-step decomposition of each eventual label event gives Z equals R plus TZ, without assuming transience, invertibility, or a renewal equation. For a service that exits almost surely on its reachable graph, this same Z is its normalized complete exit law. Complete returned snapshots may be labels for update services; actual first semantic observations may be labels for selection services.

**Theorem 1.10 (Actual event renewal equation).**

$$\forall (\operatorname{S} : \operatorname{Type}) , \forall (\operatorname{O} : \operatorname{Type}) , [\operatorname{Fintype} (\operatorname{S})] [\operatorname{Fintype} (\operatorname{O})] [\operatorname{MeasurableSpace} (\operatorname{S})] [\operatorname{MeasurableSingletonClass} (\operatorname{S})] [\operatorname{MeasurableSpace} (\operatorname{O})] [\operatorname{MeasurableSingletonClass} (\operatorname{O})] \forall (\operatorname{d} : \operatorname{S} \to \operatorname{Instruction} (\operatorname{Sum} (\operatorname{S} , \operatorname{O}))) , \operatorname{Z} (\operatorname{d}) = \operatorname{R} (\operatorname{d}) + \operatorname{T} (\operatorname{d}) \times \operatorname{Z} (\operatorname{d})$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteFairBitExitLaws.actual_renewal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The statement concerns the displayed finite primitive execution and its actual fair-tape event masses.

Applying these results to the original charged digital class still requires paid code fetching, complete field encoding, installation peak, lawful native entrances, primitive boundary semantics and the original event-tag refinement. A semantic cut does not by itself identify the original full-return output marginal. That identity requires the original exactly-one-letter protocol and almost-sure physical return. The two original same-update and positive-history compatibility clauses remain distinct. Integer determinant certificates and the four native-service common denominator are additional results.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteFairBitExitLaws.actual_renewal`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteFairBitExitLaws.exits_exit`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteFairBitExitLaws.exits_partition`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteFairBitExitLaws.finite_exit_laws`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteFairBitExitLaws.normalized_reachable_exits`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteFairBitExitLaws.path_exit`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteFairBitExitLaws.primitive_event_cut`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteFairBitExitLaws.reachable_as_exit`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteFairBitExitLaws.reachable_escape`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteFairBitExitLaws.step_mass`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteFairBitFirstReturn](FiniteFairBitFirstReturn.md)

# Native zero-trigger auxiliary histories

## Abstract

Exact-zero auxiliary histories retain all fifteen full calls and their seam configurations.

**Theorem 1.1 (The stipulated first-zero law forces the constant ready history).**

$$\operatorname{card}\left(Source\right) = 89 \land \operatorname{card}\left(Extended\right) = 610 \land \exists eta: Real, 0 < eta \land eta < \operatorname{min}\left(alpha, 2 \times pi - alpha\right) \land \forall lambda: Real, \operatorname{PuncturedDistanceLess}\left(lambda, alpha, eta\right) \implies \forall chi: \operatorname{SourceVector}\left(\right), \forall q: Source, \operatorname{chi}\left(q\right) \neq 0 \implies \operatorname{Nonempty}\left(\operatorname{NativeReaderHistory}\left(chi, q, lambda\right)\right) \land \forall h: \operatorname{NativeReaderHistory}\left(chi, q, lambda\right), \operatorname{EmptyEventTables}\left(h\right) \land \operatorname{readerConfiguration}\left(\operatorname{events}\left(h\right), 15\right) = \operatorname{readyTail}\left(\operatorname{b9}\left(q\right)\right) \land \operatorname{report}\left(\operatorname{readerConfiguration}\left(\operatorname{events}\left(h\right), 15\right)\right) = false$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/NativeReader/History.native_reader_no_jumps` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complete source and extended carriers have cardinalities 89 and 610. The native matrices and their source/tail factorization are those of Global. A source vector chi is arbitrary; the configuration q is required to satisfy chi(q) nonzero. This is the positive-support entrance condition, not an assertion that every source vector can be prepared. Every zero-support coordinate remains in the carrier and in the global vector.

NativeReaderHistory records one finite event list for each of the fifteen actual full forward calls. Each event consists of its internal physical time and the legal tail after the jump. The initial configuration is the unique original ready tail, rather than a chosen new auxiliary initialization. At every call the starting configuration is exactly the preceding call's final configuration. Events at internal time one belong to the ending call and precede report processing. There is no seam resampling or additional seam jump.

auxiliaryCallLaw expresses the stated deterministic zero-trigger rule. Before the next event the current global complex amplitude is nonzero. At the event it is exactly zero, the configuration flips only the actual addressed center along its legal two-point edge, and its new amplitude is nonzero. The recursion then uses that new configuration. An empty remaining event list requires a nonzero current amplitude throughout the remaining closed interval. currentAmplitude uses the full propagated vector without a global projective reset.

The theorem proves existence of one eta, strictly between zero and min(alpha,2*pi-alpha), working for every fixed punctured lambda, every complex source vector and every positive-support q. A native auxiliary history exists, and every history satisfying this exact event law has empty event tables, unchanged ready configuration after fifteen calls, and report b13=false. The proof obtains nonvanishing from the literal native operators, constructs the empty-event history, and rules out a first event in each successive call. Internal times, endpoint events and configuration reuse at seams are retained. The report is taken from the actual final configuration.

This theorem is the conditional auxiliary part of the full instability claim. It does not construct or assume a Bell source probability law, derive the original preparation vector from a finite allowed program, prove ideal correctness at alpha, supply the address-nine probability witness, or prove the full operator12-bound and source/archive continuation. In particular it supplies no probability or total-variation equality, no equality of ideal and actual full joint laws, and no postreport archive which consumes an ideal report. Those remain separate obligations for the complete original statement.

The event-list encoding and standard induction do not earn content. The live mathematical input is the derived source-specific uniform absence of current zeros in the exact full native pulse matrices. Counts, phase identities, conserved quadratic forms, analytic isolation and finite summation are reused or standard bookkeeping. Admission of the new source-specific inference remains subject to the independent expanded proof audit.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/NativeReader/History.native_reader_no_jumps`
- Dependency: [D5/S3/Quantum/Dynamics/NativeReader/Global](Global.md)

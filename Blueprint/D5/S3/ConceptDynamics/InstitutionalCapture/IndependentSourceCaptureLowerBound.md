# Independent-Source Capture Lower Bound

## Abstract

Independent irreplaceable branch sources impose a capture lower bound.

**Theorem 1.1 (Independent sources force one captured source per branch).**

$$\forall Source, State, Signal, Branch, Result: \operatorname{Type},\ [\operatorname{Fintype}(Branch)],\ \forall channel: Source \to State \to Signal, output: Branch \to State \to Result, source: Branch \to Source,\ (\operatorname{Injective}\left(source\right) \land\ \forall branch: Branch, candidate: Source, \operatorname{FactorsThrough}\left(output(branch), channel(candidate)\right) \iff candidate = source(branch)) \Rightarrow\ \operatorname{card}\left(Branch\right) \leq \operatorname{captureNumber}\left(channel, output\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InstitutionalCapture/IndependentSourceCaptureLowerBound.independent_source_capture_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each branch has an assigned source, distinct branches receive distinct sources, and a source determines a branch output exactly when it is that branch's assigned source.

Any finite source set that captures every branch must therefore contain the entire range of the assignment: a source witnessing capture of a branch can only be its assigned source.

The assigned-source range itself captures every branch, so admissible finite capture sets exist. Its injective cardinality is the number of branches. Inclusion in a minimum capture set then gives the lower bound.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InstitutionalCapture/IndependentSourceCaptureLowerBound.independent_source_capture_lower_bound`
- Dependency: [D5/S3/ConceptDynamics/InstitutionalCapture/CommonSourceCaptureCollapse](CommonSourceCaptureCollapse.md)

# Common-Source Capture Collapse

## Abstract

A common source channel reduces the all-branch capture minimum to one.

**Theorem 1.1 (A common source collapses the capture number).**

$$\forall Source, State, Signal, Branch, Result: \operatorname{Type}, \operatorname{Nonempty}(Branch) \Rightarrow\ \forall channel: Source \to State \to Signal, output: Branch \to State \to Result, s: Source, (\forall i: Branch, \operatorname{FactorsThrough}(output(i), channel(s))) \Rightarrow\ \operatorname{captureNumber}(channel, output) = 1.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InstitutionalCapture/CommonSourceCaptureCollapse.common_source_capture_number_eq_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source channels and branch outputs are concept readouts from the same state carrier. A controlled set compromises a branch only when one of its members determines that branch output by factorization.

The capture number minimizes the cardinality of finite source sets that compromise every branch. Nonemptiness of the branch carrier rules out capture by the empty source set.

The common source supplies a capturing singleton, while any zero-cardinal candidate would be empty and could not compromise an existing branch.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InstitutionalCapture/CommonSourceCaptureCollapse.common_source_capture_number_eq_one`

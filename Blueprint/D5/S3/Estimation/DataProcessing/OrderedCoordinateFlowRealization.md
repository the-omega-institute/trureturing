# Exact ordered-history flow and full archive realization

## Abstract

Exact ordered-history flow and full archive realization.

**Theorem 1.1 (The exact mathematical construction).**

Lean statement: `D5/S3/Estimation/DataProcessing/OrderedCoordinateFlowRealization.ordered_flow_terminal_law_realization`

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/DataProcessing/OrderedCoordinateFlowRealization.ordered_flow_terminal_law_realization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An actual archive path is defined on an arbitrary probability space. Its supplied full archives F and G retain past records, with F(t) contained in G(t) and G(t) contained in F(t+1). History is measurable before scheduling, the actual selected coordinate is measurable in G, and the obtained result is measurable afterward. Additional auxiliary records are unrestricted; the conditional cap is checked on the supplied complete G, not on a discarded history-only archive.

Scalar conditional-expectation averaging on measurable history-selection branches gives the result-flow capacity bound without a regular conditional distribution or a Standard Borel hypothesis on the original carrier. Finite disjoint branch decompositions establish all five flow constraints. The actual terminal law is defined directly from the named assignment of the terminal history; summing all ordered-history fibers proves that it equals the terminal projection of the induced flow.

For every feasible flow, cap-only rectangular row pasting permits the independently chosen totalized scheduler and result rows. The constructed finite probability space samples complete separate scheduling and result tables at each step. Its full trace atoms have the product of all scheduling-table and result-table densities. Normalization of every table law supplies the joint independence and freshness of these innovations.

The canonical pre-result archive reveals every completed table block and the entire current scheduling table, including the actual choice. It omits the current result table and all future innovations. The conditional child-event law on this full archive equals the prescribed bounded result row on the known branch. Results and scheduling tables may be retained after their use. The recursive interpreter realizes every node, selection and result mass and the exact terminal named law.

The two directions hold for heterogeneous finite alphabets, zero node or selection masses and history-dependent coordinate choices. Arbitrary original auxiliary archives are accepted in the forward direction, but their full joint law with the original seeds is not preserved by reconstruction. Cap-only row pasting is a substantive modeling assumption; a fixed external source or extra cross-branch restrictions require additional compatibility constraints. Publicly revealing a seed which determines the next result requires checking the cap on that enlarged archive and is not certified by this realization.

The terminal projection range equals the set of terminal laws of actual probability measures and legal archive paths on the finite innovation carrier. Every arbitrary-carrier archive path has its terminal law in that same set. This universal realization carrier does not restrict the original forward probability space.

**Theorem 1.2 (Exact terminal law range).**

Lean statement: `D5/S3/Estimation/DataProcessing/OrderedCoordinateFlowRealization.ordered_terminal_law_range`

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/DataProcessing/OrderedCoordinateFlowRealization.ordered_terminal_law_range` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The range of the flow projection is exactly the independently defined set of terminal laws of actual archived probability processes. The theorem also places every arbitrary-carrier legal process law in that set.

## References

- Truth anchor: `D5/S3/Estimation/DataProcessing/OrderedCoordinateFlowRealization.ordered_flow_terminal_law_realization`
- Truth anchor: `D5/S3/Estimation/DataProcessing/OrderedCoordinateFlowRealization.ordered_terminal_law_range`
- Dependency: [D5/S3/Estimation/DataProcessing/OrderedCoordinateHistoryInterpreter](OrderedCoordinateHistoryInterpreter.md)

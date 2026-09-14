# Strong Unextendibility from Refined Root Tubes

## Abstract

A complete residual-tube cover and an empty common-partner certificate exclude even one additional unbiased vector.

**Theorem 1.1 (Every covered additional point has a quantitative cross error).**

$$\operatorname{CompleteTubeAndOverlapBounds}(T, C, Q) \land \operatorname{NoCommonPartnerOfAnySixClique}(O, B) \Rightarrow\\\operatorname{ExistsCrossErrorAtLeast}(C, Q, tau).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/RootTubeStrongUnextendibility.six_frame_has_cross_error_to_any_covered_point` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take matrix-valued tubes indexed by kappa. Same-tube real trace overlaps are at least mu, within-frame overlaps are below eta, and eta is at most mu. The orthogonality and unbiasedness relations are one-sided enclosures of the actual trace conditions. For every injective orthogonality six-clique, no label is unbiased to all six labels. If every member of a six-frame C and an additional point Q lies in the complete cover, then some real trace overlap Tr(C_i Q) differs from 1/6 by at least tau.

The same-tube lower bound forces the six labels to be distinct. Their small internal overlaps place them in the orthogonality candidate relation. The empty-partner certificate supplies one forbidden cross pair for the label of Q. The unbiased enclosure then gives the stated error. This reuses the existing matrix and tube interfaces; it does not introduce a second definition of MUBs or of a projector.

The concrete research instance refines one residual tube and checks every first six-clique. Empty, overlapping and multiple-root tubes are permitted. The actual residual-sublevel cover, soundness of the refinement, and finite relation certificate must still be supplied as mathematical proofs. External checker output does not discharge these Lean hypotheses. The authoring run did not execute Lean or Scribe.

## References

- Truth anchor: `D5/S3/Quantum/Tomography/RootTubeStrongUnextendibility.six_frame_has_cross_error_to_any_covered_point`
- Dependency: [D5/S3/Quantum/Tomography/CompleteRootSupergraphExclusion](CompleteRootSupergraphExclusion.md)

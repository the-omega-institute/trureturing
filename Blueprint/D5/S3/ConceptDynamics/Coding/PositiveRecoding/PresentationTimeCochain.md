# The same time/id edge in every finite presentation basis measures actual primitive-orbit count

## Abstract

The same time/id edge in every finite presentation basis measures actual primitive-orbit count.

In the outOld basis, vertex_matrix identifies graph time with the literal nonnegative counted matrix A. dyadicGyration_nonnegative applied to A and the identity, followed by RankedTimeRecoding.relative_time and orbitChart, gives the actual primitive-orbit cardinality. closed_square is then applied to r=time and s=id; both composites equal time even if it is singular. The common K is retained and canceled. rows_id identifies the new backward matrix as the identity. This proves the same time calibration in c without assigning zero to an open chart edge.

**Theorem 1.1 (Time calibration through the same closed square).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/PresentationTimeCochain.time_calibration`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/PositiveRecoding/PresentationTimeCochain.time_calibration` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite presentation F, any finite basis c of F.V coefficient functions indexed by Fin m, and every natural d with NeZero d and hd : three divides d, let b=presentationBasis F and K=value(b,c,id,(vertex F).time). The result states both value(b,b,time,id)+K=K+value(c,c,time,id) and dyadicGyration d rows(c,c,time) 1=card(Orbit F d) in ZMod 3. No invertibility of graph time is assumed; zero vertices and empty orbit fibers remain included.

The complete native application is recorded in the ActualWordEnumeratedLoop owner narrative. Here this calibration is used at OriginalRootKernelCheck.hcal for every nonzero p divisible by three, before any specialization to three or six. No orbit-count calibration replaces arbitrary h.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/PresentationTimeCochain.time_calibration`
- Dependency: [D5/S3/ConceptDynamics/Coding/PositiveRecoding/ActualWordEnumeratedLoop](ActualWordEnumeratedLoop.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/PositiveRecoding/RankedTimeRecoding](RankedTimeRecoding.md)

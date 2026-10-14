# Original stationary integer-time marked laws

## Abstract

Original stationary integer-time marked laws

Presentation retains every finite hidden alphabet H, nonnegative real probability row lambda and nonnegative binary emission matrices M. The sum M(false)+M(true) is stochastic and leaves lambda stationary; the weighted two-one mass is zero. No positive stationary mass, communication, period, synchronization or unifilarity assumption is added. PathSpace is the existing pair of integer-indexed hidden and emitted paths. visibleCylinder observes the original consecutive integer output coordinates, with no observations at length zero. shift translates both original clocks by the same integer.

**Theorem 1.1 (Measurability of original marked cylinders).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalMarkedLaw.cylinder_measurable`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalMarkedLaw.cylinder_measurable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite measurable hidden alphabet with measurable singletons, every integer start, every natural length and every hidden/output word, the original marked cylinder is measurable. It is the intersection of the hidden-coordinate and output-coordinate equality events. Original future factorization uses these measurable cylinders.

**Theorem 1.2 (Nonnegative original path products).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalMarkedLaw.path_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalMarkedLaw.path_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original Presentation theta, every natural length and every hidden/output word, pathMass of its nonnegative original emission matrices is nonnegative. This bounds the finite future row sums and their actual conditional cylinder measures.

**Theorem 1.3 (Summing the future hidden coordinates).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalMarkedLaw.sum_path_tails`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalMarkedLaw.sum_path_tails` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original Presentation theta, natural length n, source hidden state i and output word w, the sum over all hidden tails h of pathMass(M,n,Fin.cons(i,h),w) equals futureMass(M,i,n,w). The empty word uses the identity matrix. This identity is used by the complete actual future-law and screening construction.

**Theorem 1.4 (Visible pushforward cylinders).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalMarkedLaw.visible_masses`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalMarkedLaw.visible_masses` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every such presentation, every probability J satisfying all HasOriginalCylinders equalities, every integer start, every natural length and every Boolean word, the actual visible measure J.map Prod.snd assigns its visible cylinder the real mass sum over i of lambda(i) futureMass(i,n,w). futureMass is the row sum of the original matrix word product, with the identity matrix at length zero. No output table is supplied independently of J.

A visible event is the finite disjoint union of its complete hidden-path cylinders. Summing the original path products over hidden tails recursively gives the corresponding row sum of wordMatrix. The existing path_step and sum_paths algebra in MarkedPredictiveQuotient is used directly. Zero initial and transition weights contribute zero, and length zero recovers total mass one.

**Theorem 1.5 (Support on the full two-sided no11 space).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalMarkedLaw.visible_no11`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalMarkedLaw.visible_no11` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every probability J with the original cylinders, its actual visible pushforward almost surely has no adjacent pair of true symbols at any integer time. The length-two visible-cylinder mass is exactly the weighted M(true) squared mass assumed zero by Presentation. The integer intersection of these full-measure events gives simultaneous two-sided support. This statement does not delete any zero-probability words or assume that ghost-state matrix products vanish.

**Theorem 1.6 (Existence and stationarity on the original integer clock).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalMarkedLaw.original_law`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalMarkedLaw.original_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite presentation with measurable singletons there exists a probability J on the existing PathSpace H with every HasOriginalCylinders equality at every integer start and every natural length, including zero. J is invariant under every integer shift. Its actual visible pushforward has the matrix-product visible-cylinder masses and almost-sure no11 support described above. The finite hidden measurable structure is discrete; normalization excludes an empty hidden alphabet.

Use the finite arriving-symbol state space H times Bool. Its initial mass at (j,y) is the sum over i of lambda(i) M(y)(i,j); its transition from (i,x) to (j,y) is M(y)(i,j). Stochasticity normalizes its rows, and the original stationary equation makes its arriving-symbol initial law stationary. Every finite chain-block mass is the product of these entries and its initial mass. Right marginalization uses stochasticity; left marginalization uses stationarity, so cropping any interval preserves the appropriate block law.

The symmetric finite windows have surjective total restriction maps and compatible probability laws. InverseLimitProbabilityExtension.exists_unique_probability_extension supplies their actual thread law. Compatible threads reconstruct integer paths measurably, and every integer interval is contained in a sufficiently large symmetric window. The uniqueness supplied on threads identifies every translated law. This is the extension argument used for the specialized bilateral construction in ParryBilateralLaw, applied here to an arbitrary stationary finite chain; the general extension theorem itself is reused.

Read H(t) from the hidden component at time t and X(t) from the arriving symbol at time t+1. For a fixed original marked cylinder the finite arriving-symbol block has precisely two possibilities for its unconstrained first symbol. Summing those two masses gives lambda(h(0)) times the original marked path product. This proves all original cylinders without assuming them, using no division at a zero entry. MarkovPrefixMass supplies natural-time prefix masses for a trajectory law, but a natural-time law alone is insufficient for this conclusion and is not used as a replacement for the bilateral extension.

The theorem supplies law construction and visible support. Universal future screening, retained-exterior conditional expectations, both squared erasure comparisons, infinite future-law identification, marked quotient laws, MAP domination, strict affinity, geometric contraction and summability require their separate same-law bridges. No attainment or all-dimension separation conclusion is asserted.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalMarkedLaw.cylinder_measurable`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalMarkedLaw.original_law`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalMarkedLaw.path_nonneg`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalMarkedLaw.sum_path_tails`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalMarkedLaw.visible_masses`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalMarkedLaw.visible_no11`
- Dependency: [D5/S3/Estimation/DataProcessing/InverseLimitProbabilityExtension](../../../Estimation/DataProcessing/InverseLimitProbabilityExtension.md)
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/MarkedPredictiveQuotient](MarkedPredictiveQuotient.md)

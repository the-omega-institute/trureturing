# Chronological rise counts before and at the first marker

## Abstract

Actual acquired 01 transitions in an absorbing adaptive two-arm execution.

**Theorem 1.1 (Every active acquired prefix alternates and has the actual rise count).**

$$\begin{gathered}\forall U:Type, [\operatorname{MeasurableSpace}\left(U\right)],\\{}\forall p:\operatorname{Policy}\left(U\right), \forall u:U, \forall z:Source, \forall n\in\mathbb{N},\\{}(\operatorname{noAdjacentOnes}\left(z\right)\land n<\operatorname{stoppingTime}\left(p, u, z\right))\Rightarrow\\{}((\forall s:Bool, \forall i\in\mathbb{N}, i\le\operatorname{sideCount}\left(\operatorname{actions}\left(\operatorname{actualRun}\left(p, u, z, n\right)\right), s\right)\Rightarrow\operatorname{endpoint}\left(z, s, i\right)=\operatorname{alternatingBit}\left(\operatorname{root}\left(z\right), i\right))\\{}\land(\forall s:Bool, \operatorname{actualRiseCount}\left(p, u, z, s, n\right)=\operatorname{if} \operatorname{root}\left(z\right) \operatorname{then} \lfloor\frac{\operatorname{sideCount}\left(\operatorname{actions}\left(\operatorname{actualRun}\left(p, u, z, n\right)\right), s\right)}{2}\rfloor \operatorname{else} \lfloor\frac{\operatorname{sideCount}\left(\operatorname{actions}\left(\operatorname{actualRun}\left(p, u, z, n\right)\right), s\right)+1}{2}\rfloor))\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/AdaptiveActualRiseCounts.actual_rise_count_before_stop` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The telescope retains every original measurable seed space, Policy, seed and Source. For every natural n strictly below stoppingTime and every side s, let c be sideCount of the actions of actualRun at n. Every endpoint at i at most c equals alternatingBit(root(z),i), so both prefixes start at the same original root. The actual chronological 01 count is floor(c/2) for root true and floor((c+1)/2) for root false.

The inequality uses the natural-number inclusion into WithTop naturals. Infinity is allowed as stoppingTime: no future finite stop, termination assumption, probability law, finite mean, independence or restriction on switching is needed. The private all-time transport connects chronological acquisitions to each original arm rank, including absorbed states. Frozen replay and alternating-prefix results and the pinned residue-cardinality theorem supply the remaining steps. The first-stop theorem below consumes this consequence at n = T minus one.

**Theorem 1.2 (Actual rises equal preterminal alternating half-lengths).**

$$\begin{gathered}\forall U:Type, [\operatorname{MeasurableSpace}\left(U\right)],\\{}\forall p:\operatorname{Policy}\left(U\right), \forall u:U, \forall z:Source, \forall T\in\mathbb{N},\\{}(\operatorname{noAdjacentOnes}\left(z\right)\land\operatorname{stoppingTime}\left(p, u, z\right)=T)\Rightarrow(0<T\land(\forall s:Bool,\\{}(\operatorname{actualRiseCount}\left(p, u, z, s, T\right)=\operatorname{actualRiseCount}\left(p, u, z, s, T-1\right))\land(\operatorname{actualRiseCount}\left(p, u, z, s, T\right)=\operatorname{if} \operatorname{root}\left(z\right) \operatorname{then} \lfloor\frac{\operatorname{sideCount}\left(\operatorname{zeroReplay}\left(p, u, T-1\right), s\right)}{2}\rfloor \operatorname{else} \lfloor\frac{\operatorname{sideCount}\left(\operatorname{zeroReplay}\left(p, u, T-1\right), s\right)+1}{2}\rfloor)))\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/AdaptiveActualRiseCounts.actual_rise_count_at_first_stop` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Source, Policy, actualRun, sideCount, zeroReplay and stoppingTime are those of AdaptiveMarkerStoppingTails. False and true select the left and right arms. The source has one Boolean root and two original infinite bit paths. The policy uses its original seed and the acquired action and reply lists; switching sides is unrestricted.

For each chronological index k below n, actualRiseCount(p,u,z,s,n) counts k exactly when h = actualRun(p,u,z,k) is not stopped, the policy chooses s at h, and the original edge at sideCount(h.actions,s) has inner endpoint false and outer arm label true. Thus the count is over actual acquired edges, including the final query index when n = T. The final query is 00 and contributes zero to both sides.

Here root(z) is the source's Boolean first coordinate, and subtraction and division are natural-number operations. The theorem quantifies both roots, every measurable seed space, every policy and seed, every source with no adjacent ones, and every finite first stopping time T. The preterminal arm lengths are read from zeroReplay at T minus one. No probability law or finite mean is assumed.

The active-prefix theorem identifies chronological rise counts with counts along each actually acquired arm prefix by induction on execution time, including absorbed states. The stopped_execution_replay_bridge identifies the preterminal actions with zeroReplay. The no_marker_iff_alternating_prefix theorem then identifies the bit prefix, and the pinned natural-number residue count gives its half-length.

This is the finite edge-count identity used for the success exponents in the joint-parameter stopping experiment. It supplies no density formula, measurable archive bijection, almost-sure termination, tail estimate or parameter recovery. The latent endpoints occur in the mathematical count and its proof; no new observable port or continued execution after stopping is asserted.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/AdaptiveActualRiseCounts.actual_rise_count_at_first_stop`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/AdaptiveActualRiseCounts.actual_rise_count_before_stop`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/AdaptiveMarkerStoppingTails](AdaptiveMarkerStoppingTails.md)

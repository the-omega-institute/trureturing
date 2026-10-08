# Actual stopping, zero replay, and exact tails

## Abstract

Exact adaptive marker tails under a shared-root Markov source and an arbitrary independent seed law.

**Theorem 1.1 (First-hit execution and acquired query cost).**

$$\begin{gathered}\forall U:Type, (\operatorname{MeasurableSpace}\left(U\right)\Rightarrow(\\{}\forall p:\operatorname{Policy}\left(U\right), \forall u:U, \forall s:Source, \forall n\in\mathbb{N},\\{}(((n<\operatorname{stoppingTime}\left(p, u, s\right))\Leftrightarrow\operatorname{prefixNoMarker}\left(s, \operatorname{zeroReplay}\left(p, u, n\right)\right))\land\\{}((\operatorname{stopped}\left(\operatorname{actualRun}\left(p, u, s, n\right)\right)=false)\Leftrightarrow\operatorname{prefixNoMarker}\left(s, \operatorname{zeroReplay}\left(p, u, n\right)\right))\land\\{}((\operatorname{stopped}\left(\operatorname{actualRun}\left(p, u, s, n\right)\right)=false)\Rightarrow((\operatorname{actions}\left(\operatorname{actualRun}\left(p, u, s, n\right)\right)=\operatorname{zeroReplay}\left(p, u, n\right))\land(\operatorname{replies}\left(\operatorname{actualRun}\left(p, u, s, n\right)\right)=\operatorname{replicate}\left(n, false\right))\land(\operatorname{actualQueryCount}\left(p, u, s, n\right)=n)))\land\\{}((\operatorname{stopped}\left(\operatorname{actualRun}\left(p, u, s, n\right)\right)=true)\Rightarrow(\forall k\in\mathbb{N}, (\operatorname{actualRun}\left(p, u, s, n+k\right)=\operatorname{actualRun}\left(p, u, s, n\right))))\land\\{}(\operatorname{noAdjacentOnes}\left(s\right)\Rightarrow((n<\operatorname{stoppingTime}\left(p, u, s\right))\Leftrightarrow\operatorname{alternatingPrefixes}\left(s, \operatorname{zeroReplay}\left(p, u, n\right)\right)))\land\\{}(\operatorname{actualQueryCount}\left(p, u, s, n\right)=\operatorname{min}\left(n, \operatorname{stoppingTime}\left(p, u, s\right)\right))))).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/AdaptiveMarkerStoppingTails.stopped_execution_replay_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A policy reads its seed and its acquired action and reply lists, stored newest first. Every active step queries a fresh edge on the chosen arm. The first 00 response stops execution; every later step preserves the complete state and acquires no query.

The stopping time is the first actual stopped state, with infinity allowed. Its tail event equals the no-marker prefixes at the arm counts from the same policy's all-zero replay. Replay takes no source argument. Under no adjacent ones, these prefixes are alternating. Acquired query count is the minimum of elapsed steps and first-hit time.

**Theorem 1.2 (Both exact tails with the original-seed odd-odd probability).**

$$\begin{gathered}\forall U:Type, (\operatorname{MeasurableSpace}\left(U\right)\Rightarrow(\\{}\forall v:\operatorname{Measure}\left(U\right), (\operatorname{ProbabilityMeasure}\left(v\right)\Rightarrow(\\{}\forall p:\operatorname{Policy}\left(U\right), \forall \alpha\in[0,1], \forall q\in[0,1],\\{}((\forall m\in\mathbb{N}, \operatorname{Tail}\left(\operatorname{jointLaw}\left(v, \alpha, q\right), p, 2m+1\right)=(\alpha+(1-\alpha)q)q^{m})\land\\{}(\forall m\in\mathbb{N}, ((1\leq m)\Rightarrow(\operatorname{Tail}\left(\operatorname{jointLaw}\left(v, \alpha, q\right), p, 2m\right)=q^{m}+\operatorname{lambda}\left(p, v, m\right)(\alpha+(1-\alpha)q^{2}-q)q^{m-1})))\land\\{}(\forall m\in\mathbb{N}, 0\leq\operatorname{lambda}\left(p, v, m\right)\leq1)))))).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/AdaptiveMarkerStoppingTails.adaptive_marker_stopping_tails` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Tail denotes the real measure of the actual event that stoppingTime exceeds the stated depth. The source law first mixes a Bernoulli root of mass alpha at true. Given this root and one fixed q, its two outward arms are independent Markov trajectories with transition rows (1-q,q) and (1,0). The same q is used for every transition on both arms.

The joint law is the product of this source law and the original arbitrary probability measure on the measurable seed space. Policy requires every fixed finite action/reply history gives a measurable seed section; the policy has no hidden-source argument.

Lambda is the original seed measure of the event that zeroReplay at depth twice m has odd counts on both arms. Its definition contains no q, source, or survival conditioning. The proof derives trajectory support from the Markov kernel, calculates alternating finite-prefix masses, and integrates the actual survival event over the original seed law. The formulas hold on the closed unit interval and therefore for the chapter's strictly interior parameters.

**Theorem 1.3 (One-query all-zero extension).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/AdaptiveMarkerStoppingTails.prefix_no_marker_cons`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/AdaptiveMarkerStoppingTails.prefix_no_marker_cons` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every source, finite action history and chosen arm, the extended all-zero prefix holds exactly when the old prefix holds and the next native marker response is false.

**Theorem 1.4 (Root and forbidden-adjacency support).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/AdaptiveMarkerStoppingTails.path_support`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/AdaptiveMarkerStoppingTails.path_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every unit-interval parameter and Boolean root, almost every arm starts at that root and contains no adjacent pair of true bits.

**Theorem 1.5 (Successive alternating bits).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/AdaptiveMarkerStoppingTails.alternating_bit_succ`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/AdaptiveMarkerStoppingTails.alternating_bit_succ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every Boolean root and natural index, the next alternating bit is the Boolean negation of the current bit.

**Theorem 1.6 (Alternating arm cylinder mass).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/AdaptiveMarkerStoppingTails.arm_alternating_mass`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/AdaptiveMarkerStoppingTails.arm_alternating_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every unit-interval parameter, Boolean root and natural length, the alternating prefix mass is the parameter raised to half the length rounded down for a true root and up for a false root.

**Theorem 1.7 (Measurable zero cylinders).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/AdaptiveMarkerStoppingTails.measurable_set_no_marker_cylinder`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/AdaptiveMarkerStoppingTails.measurable_set_no_marker_cylinder` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every pair of natural arm lengths, the all-zero marker cylinder is measurable.

**Theorem 1.8 (Alternation characterizes no marker).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/AdaptiveMarkerStoppingTails.no_marker_iff_alternating_prefix`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/AdaptiveMarkerStoppingTails.no_marker_iff_alternating_prefix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every Boolean path starting at a fixed root and forbidding adjacent true bits, absence of adjacent false bits before a finite length is equivalent to the alternating prefix through that length.

**Theorem 1.9 (Both independent arms satisfy support).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/AdaptiveMarkerStoppingTails.paired_path_support`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/AdaptiveMarkerStoppingTails.paired_path_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every unit-interval parameter and Boolean root, almost every pair under the product arm law consists of two paths starting at that root and forbidding adjacent true bits.

**Theorem 1.10 (Two-arm root-conditioned cylinder mass).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/AdaptiveMarkerStoppingTails.conditional_no_marker_cylinder_mass`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/AdaptiveMarkerStoppingTails.conditional_no_marker_cylinder_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every unit-interval parameter, Boolean root and two natural arm lengths, the two-arm all-zero marker cylinder has mass equal to the parameter raised to the sum of the root-dependent half-length exponents.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/AdaptiveMarkerStoppingTails.adaptive_marker_stopping_tails`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/AdaptiveMarkerStoppingTails.alternating_bit_succ`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/AdaptiveMarkerStoppingTails.arm_alternating_mass`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/AdaptiveMarkerStoppingTails.conditional_no_marker_cylinder_mass`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/AdaptiveMarkerStoppingTails.measurable_set_no_marker_cylinder`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/AdaptiveMarkerStoppingTails.no_marker_iff_alternating_prefix`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/AdaptiveMarkerStoppingTails.paired_path_support`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/AdaptiveMarkerStoppingTails.path_support`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/AdaptiveMarkerStoppingTails.prefix_no_marker_cons`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/AdaptiveMarkerStoppingTails.stopped_execution_replay_bridge`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/MarkovPrefixMass](TrajectoryLaws/MarkovPrefixMass.md)

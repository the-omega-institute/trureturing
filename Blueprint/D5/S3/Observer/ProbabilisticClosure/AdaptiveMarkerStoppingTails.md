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

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/AdaptiveMarkerStoppingTails.adaptive_marker_stopping_tails`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/AdaptiveMarkerStoppingTails.stopped_execution_replay_bridge`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/MarkovPrefixMass](TrajectoryLaws/MarkovPrefixMass.md)

# Original cylinders at a future-output cut

## Abstract

Original cylinders at a future-output cut

PathSpace H carries the original integer hidden and output coordinates. future(t,z)(k) is X(t+k), for every natural k. past(t,z)(k) is the pair (H(t-k-1),X(t-k-1)). These are the complete future-output and strictly earlier marked half-lines. state(t,z) is H(t), so X(t) belongs to the future and H(t) is the conditioning boundary. All maps use the original emitted-bit clock.

**Theorem 1.1 (Actual finite factorization at every integer boundary).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalFutureCylinders.past_future_mass`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalFutureCylinders.past_future_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix any finite hidden alphabet with measurable singletons, any original Presentation theta, and any probability J satisfying its proved original cylinders. For every integer t, natural lengths m and n, hidden word h of length m+1, past output word w of length m and future output word v of length n, the J real mass of cylinder(t-m,m,h,w) intersected with the visible v cylinder starting at t equals lambda(h(0)) times pathMass(M,m,h,w) times futureMass(M,h(m),n,v). The past cylinder includes H(t), while its last output is X(t-1). Length zero, zero weights and arbitrary stochastic successor mixtures are included.

Append every possible future hidden tail to the fixed past hidden word. The resulting full original marked cylinders form a disjoint union of the event being measured. Their path products split at H(t); summing the future hidden tails uses OriginalMarkedLaw.sum_path_tails. This establishes the finite factorization from the actual original cylinder law.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalFutureCylinders.past_future_mass`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalMarkedLaw](OriginalMarkedLaw.md)

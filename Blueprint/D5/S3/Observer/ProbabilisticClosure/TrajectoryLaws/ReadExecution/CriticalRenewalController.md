# The counted critical renewal controller

## Abstract

Both decisions and every paid read of one counted renewal controller.

**Definition 1.1 (The complete past on the same source).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalController.history`

*Formalization.* `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalController.history` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A sample consists of one natural initial wait and a sequence of finite blocks. Each block records all fresh outcomes on its zero reads and its closing tick. For every natural n, history(n) is the pair of that initial wait and the restriction of the sequence to indices strictly smaller than n. These are proof coordinates and are not persistent configurations of the observer.

**Definition 1.2 (The filtration of full completed blocks).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalController.filtration`

*Formalization.* `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalController.filtration` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every n, filtration(n) is the sigma algebra pulled back along history(n). Its monotonicity follows by restricting a longer finite block history to a shorter one. It contains the initial wait and every zero and tick coin in the first n blocks. Under sourceLaw, the next full block is independent of this sigma algebra. Conditional means and second moments of its own increment therefore equal integrals under its actual joint gap-mark law; the duration and mark of that block are never separated into independent marginals.

**Theorem 1.3 (One table with both risks and paid means).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalController.uniform_counted_controller`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalController.uniform_counted_controller` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix any natural r at least one, positive real c, and real alpha strictly between zero and one half. There exist positive eta, s0, D, V and C, with eta and s0 smaller than one. Define lambda=min(1,D/(2 exp(1) V)), A=log(1/alpha)/lambda and K=4A+4. These constants are chosen before every s and J. For every positive s smaller than s0 and every natural J at least one satisfying s times 2^J at most eta, use the separately normalized gapLaw and equilibrium waitLaw of CriticalRenewalSource under each Boolean label.

Under label i let m(i) be rewardMean(r,J,gapLaw(i)). The common immutable tick is roundedTick(reward(r,J),theta,delta), where theta=(m(false)+m(true))/2 and delta=J/2^(rJ). Put Delta=m(true)-m(false) and H=ceil(A/delta). H is positive. Every phase and evidence state belongs to the carrier State(H,J) of CriticalRenewalTable. Its entire cardinality is exactly 3+(2H-1)(J+1), including the wait, two labels and every interior integer evidence crossed with every alive or dead phase. Its real cardinality is at most K times 2^(rJ). For every block sequence and natural n, the integer evidence equals score(delta,n)/delta.

For each label i, on the same sourceLaw and same selected tick, the probability that run at the actual paidStop emits the opposite label is at most alpha. Both the completed-gap stop and paidStop are finite almost surely. Their real natural-value projections are integrable. The expected completed-gap count is at most 2(A+3/2)/Delta. The exact paid expectation is 1+beta(i)+mean(i) times the expected completed-gap count. The paid expectation under each label is at most C divided by s^(2r+1) J. Thus both wrong-decision bounds, both almost-sure paid stops and both finite paid means hold simultaneously.

Almost surely the paid stopping time is exactly 1 plus the initial wait plus the sum, over all blocks strictly before gapStop, of that block's zero count plus one. At that actual paid read the run equals target of its completed-block integer evidence. Every holding read, zero after phase death and the final closing tick is charged. The evidence and phase are the only active retained distinctions. The run uses the next consecutive actual bit and its fresh row outcome, and the source continues without a reset.

The conditional moments follow from independence of the next complete block from the initial wait and past complete blocks. uniform_one_gap supplies the source-specific unconditional moments of this same rounded tick. The exact real threshold exit is identified with gapStop. critical_renewal_stopping_risks first obtains finite stopped drift, overshoot and integrable gap exit, and only then takes the bounded exponential limit for the two wrong exits. stopped_prefix_payment identifies those exits with the internally emitted labels and the literal paid clock. actual_source_payment uses predictable inclusion of the next duration to derive the exact expectation without score-duration independence.

The scalar neighborhood bounds mean(i) by Cmu/s and 1+beta(i) by Cbeta/s. The lower signal bound is D s^(2r) J. For all allowed caps, s^(2r) J is at most one; this absorbs the initial-wait term with the same constant C=Cbeta+2 Cmu(A+3/2)/D. The state bound uses H at most A 2^(rJ)/J+1, J+1 at most 2J, and J+1 at most 2^(rJ). The restriction to one common neighborhood precedes all caps and any configuration budget.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalController.filtration`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalController.history`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalController.uniform_counted_controller`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalOneGap](CriticalRenewalOneGap.md)
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalPayment](CriticalRenewalPayment.md)

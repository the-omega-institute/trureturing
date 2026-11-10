# The original renewal source pair

## Abstract

Literal degree-nine gap and stationary first-wait distributions.

**Definition 1.1 (The literal positive-gap distributions).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/OriginalRenewalLaws.gapLaw`

*Formalization.* `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/OriginalRenewalLaws.gapLaw` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For one common real q with 0<q<1, the false label uses F(k)=k^9. The true label uses the literal rational-center degree-nine polynomial Hc: its correction numerator has coefficients 55800726477138, -224986136658885, 420664314485485, -540138133491075, 518234977000797, -254383031435085, 77668004560980 and 43377331415040 at degrees one through eight, divided by 35 times 10^24.

For each label the unnormalized weight is zero at k=0 and F(k)q^k at every positive natural k. Its exact normalizer is the infinite sum of those weights. The probability mass function is the nonnegative density obtained by dividing by that normalizer. The polynomial is positive at every real x at least one: bound each negative lower power by x^9 and retain all positive terms. Polynomial geometric summability gives a finite, positive normalizer for every common q in the entire open unit interval.

**Definition 1.2 (The stationary first wait, including zero).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/OriginalRenewalLaws.waitLaw`

*Formalization.* `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/OriginalRenewalLaws.waitLaw` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The gap K counts zeros, so the intertick mean mu is the exact sum of (k+1) times the gap density. For every natural u, including zero, the first-wait mass is the sum of gap masses at k>=u divided by mu. The density at k=0 vanishes, so this is also the sum over k>=max(1,u). The sum of these tails equals mu because a mass at k contributes once at each u from zero through k. This counting identity and polynomial geometric summability prove that waitLaw is a probability mass function. No finite cutoff, small-parameter restriction or auxiliary moment assumption is used.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/OriginalRenewalLaws.gapLaw`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/OriginalRenewalLaws.waitLaw`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalTable](CriticalRenewalTable.md)

# The original renewal source and joint laws

## Abstract

Literal degree-nine renewal inputs and their original finite joint execution law.

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

**Theorem 1.3 (The entire finite joint execution law).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/OriginalRenewalLaws.finite_execution_law`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/OriginalRenewalLaws.finite_execution_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a finite complete configuration carrier C with measurable singletons, an emission tag, and two configurations carrying its two Boolean decisions. An original stochastic specification gives a joint initialization distribution and, for every complete configuration and acquired bit, a joint distribution of the intermediate configuration and ensuing action. A read action carries a none-tagged complete configuration; an emitted action carries a configuration with its own decision tag. These original joint distributions are specified without any innovation tape, and can correlate the update and action choice.

One fresh innovation is a finite table with one joint outcome for every configuration and bit. Its distribution is the product of all original operation rows. The machine evaluates only the entry indexed by its actual complete configuration and newly read bit. Initialization samples the original joint initialization law. The table and initialization outcome are source independent. Neither table, source name, clock, acquired receipt nor unused random choices are retained in C.

For every fixed source bit sequence and every natural allowance n, the original joint execution distribution is defined recursively by the original initialization and operation rows. Its vector records n+1 successive joint outcomes. After internal emission its previous outcome is held, with no read or operation. The table interpreter on an independent seed and n independent fresh tables has exactly this entire vector distribution. The statement retains both intermediate configurations and their correlated ensuing actions, and includes initial emission, arbitrary terminal configurations, null paths and allowance zero. It is an equality of measures on the complete finite trace space, not only of one-operation marginals.

The induction separates the last fresh table from the preceding seed and tables. It transports the complete preceding trace distribution and integrates the selected original joint row. The finite table is an analytical representation of fresh randomness, not an accessible persistent random tape. The same original stochastic specification serves both source labels. The common realization also transports this finite representation to the independent infinite innovation product and identifies its actual actions with the original execution. No entropy, occupation or full E4 conclusion is asserted by the finite execution identity.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/OriginalRenewalLaws.finite_execution_law`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/OriginalRenewalLaws.gapLaw`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/OriginalRenewalLaws.waitLaw`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalTable](CriticalRenewalTable.md)
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/OriginalObserverNormalization](OriginalObserverNormalization.md)

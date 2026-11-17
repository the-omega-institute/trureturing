# Original observer execution normalization

## Abstract

Original joint actions preserve their acquired prefix, exact paid cost and internal decision in the read-ready boundary representation.

**Theorem 1.1 (Original actions and boundary simulation).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/OriginalObserverNormalization.execution_normalization`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/OriginalObserverNormalization.execution_normalization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A machine has one complete configuration carrier C, an internal emission tag C to Option Bool, and two configurations carrying the respective decision tags. A chosen action either reads from a configuration whose tag is none or emits its configuration's own Boolean tag. The configuration uniquely determines the chosen action: no extra persistent phase or decision field is available. Initialization first computes a configuration and then chooses an action using the same initialization innovation. Each paid operation reads one bit, computes its update, and chooses the ensuing action. Both maps may use the old configuration, the newly acquired bit and the same fresh operation innovation; the ensuing choice also receives the update result. Thus an update and a stop may be correlated, even when the bit is not retained in the next live configuration.

The initialization and operation primitives receive no source index, age, clock, read count, old receipt or future innovation. Both their intermediate configuration values and their retained configurations belong to C. The action choice completes within the initialization or paid operation; there is no additional persistent silent-step machine. Every retained control phase, seed or choice must already be included in C. This formulation represents the joint primitive operations of the finite-observer definition; its admissibility as a model of that definition includes this complete-configuration requirement.

The original interpreter execute is defined independently of the renewal run. Its external receipt starts empty. A read action obtains exactly the bit and innovation at the receipt length, appends that bit, and performs the original joint operation. An emit action returns the same receipt and internal label without reading. The receipt is a mathematical account of the read port and is never supplied to an observer primitive. A finite scheduler allowance continues analytically after emission, with no further operation or payment.

The boundary carrier is the disjoint union of all none-tagged configurations and the two Boolean decisions. It includes unreachable live configurations. Only already emitted configurations with the same decision are identified. The normalized update applies the original joint operation at a live boundary and preserves an emitted label pointwise. For every initialization innovation, every original operation-innovation sequence, every natural initial wait, every natural gap sequence and every finite allowance n, the normalized original action equals ActualRenewalStopping.run at n. The original receipt is exactly the consecutive source prefix of its own length; whenever the original action is still live, that length equals n.

The induction uses the original receipt length to identify the next paid bit and coin with index n only while the original interpreter is live. Its emitted case performs neither acquisition nor coin evaluation. The statement includes initial emission, stops in initial or later zeros, a stop on a tick, zero-length zero words, all original innovation values and nonemitting paths. It makes no replacement of the original innovation space and excludes no null paths.

**Theorem 1.2 (Same budget, original stopping receipt and internal label).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/OriginalObserverNormalization.stopping_normalization`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/OriginalObserverNormalization.stopping_normalization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original stopIndex is the least allowance at which execute internally emits, or none when there is no such allowance. It is defined before the target first-hit time. The original result is Option of a receipt and a Boolean label, formed from that original stop and its action output. The original paidCost is its receipt length and the original decision is its internally emitted label. Both are defined before the target firstHit, with none for nonemission.

Fix common probability measures kappa and rho on the original initialization and operation innovations. Require measurability of the normalized original initialization and, for every complete configuration and bit, of the normalized original joint outcome as a function of its operation innovation. The theorem extracts eta from the initialization pushforward, with its exact singleton mass, and A and B from the effective zero and one operation pushforwards. B is the tick row denoted C in the renewal formulas. Joint state/innovation measurability follows by the finite state partition. Both decision rows are proved pure self-loops. These common witnesses are chosen before all initialization outcomes, coin streams, waits and gaps are quantified, so the same eta,A,B serve both sources. No transition, cylinder or stopping law is assumed as a field of the machine.

For a finite C of cardinality at most M, the boundary carrier also has cardinality at most M: embed each live configuration as itself and each decision as its already counted original label. The disjointness of the emission tags proves injectivity. In particular no M+2 carrier or duplicated control phase is introduced. The original stopIndex equals firstHit of the normalized run. At a finite first emission t, the original receipt has length exactly t and is the source prefix of length t. The result therefore equals the target first-hit result with precisely that prefix and the normalized state's internal label, including the none nonemission outcome.

The first-emission cost assertion uses minimality in the original interpreter: if t is positive, its predecessor is a read action with a receipt of length t-1, so the last operation appends exactly one bit. It does not define the original cost or decision from a new process. With the original first emission identified, the existing actual-renewal stopping consumer applies to the same original innovation sequence. The first terminal analytical epoch has the same emitted label, and its index is bounded by the number of already paid ticks and hence by the original receipt length. Its index is zero exactly when the original first-emission cost T satisfies T <= wait + 1. Unread suffix bits add no payment.

The simulation holds under either source on the original innovation space, including null innovation paths. The supplied innovation measures must be those of the original source-independent initialization and fresh operations; the row extraction is their one-operation pushforward and requires no division by a history mass. This does not itself construct the joint source/innovation probability space or prove its finite-cylinder law. Realization of the two source measures, ordinary-history probability consumers, matrix-series identification, occupation expectations, entropy and the full harmonic comparison require their respective hypotheses. No such downstream conclusion follows merely from the deterministic simulation.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/OriginalObserverNormalization.execution_normalization`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/OriginalObserverNormalization.stopping_normalization`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/ActualRenewalPrefixLaw](ActualRenewalPrefixLaw.md)

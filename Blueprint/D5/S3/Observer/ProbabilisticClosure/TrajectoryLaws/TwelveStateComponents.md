# Native positive stationary hidden components

## Abstract

Native positive stationary hidden components

Every component is a restriction of the original alternative presentation: it uses the same marked entries and a positive normalization of its actual stationary row. The conclusion concerns complete output measures on the original emitted-bit clock.

**Theorem 1.1 (A native stationary component of an ergodic output law).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/TwelveStateComponents.ergodic_native_component_law`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/TwelveStateComponents.ergodic_native_component_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any stationary finite marked presentation θ whose output law is ergodic, every finite original hidden subset C and stationary restriction κ with the same marked entries and c times its stationary masses equal to the original masses, for some positive c, has complete visible law equal to θ. Restricted word path sums give scaled cylinder domination. A finite symmetric window partitions each measurable cylinder into original word atoms. Approximation under the sum of the two probability measures extends domination to absolute continuity on all output events. Stationarity of κ and ergodic extremality then give equality. The exact actual-native-component theorem consumes this helper; it also supplies the general ergodic-component clause of the supported-word obstruction.

**Theorem 1.2 (Every positive native irreducible component retains the same actual law).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/TwelveStateComponents.actual_native_component`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/TwelveStateComponents.actual_native_component` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite stationary presentation θ with complete visible law equal to the twelve-state P, every finite hidden subset C, every stationary stochastic presentation κ on C and every positive real weight c, assume c times κ.initial(i) equals θ.initial(i), and every κ marked entry is the corresponding original θ entry. If κ has positive-power reachability between every pair, its complete visible law equals P and all its word products exclude nonempty exact positive rectangular support. The proof first bounds the actual restricted path sums and every scaled cylinder mass by the original ones, extends that domination to absolute continuity on the complete bilateral output space, and uses original output ergodicity and component stationarity. It then applies the actual same-law irreducible obstruction. Periodic components remain allowed; zero-weight ghosts remain outside this conclusion.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/TwelveStateComponents.actual_native_component`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/TwelveStateComponents.ergodic_native_component_law`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/TwelveStateErgodicity](TwelveStateErgodicity.md)

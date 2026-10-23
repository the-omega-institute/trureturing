# Fixed-target recovery and unattained stopping error

## Abstract

Fixed-target recovery and unattained stopping error

**Definition 1.1 (The raw nested past fields).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FixedTargetRecovery.pastInformation`

*Formalization.* `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FixedTargetRecovery.pastInformation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The natural-indexed filtration has field pastField(r) at radius r. Each chronological past word is a measurable projection of the next longer word, and all fields lie in the original joint process field.

**Definition 1.2 (Actual fixed-target MAP choices).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FixedTargetRecovery.fixedMAP`

*Formalization.* `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FixedTargetRecovery.fixedMAP` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At every natural radius r and every Boolean word of length r, fixedMAP is the labelEquiv image of the original current_map_error cell-mass maximizer. Null words retain the same total selected choice.

**Definition 1.3 (Native actual posterior coordinates).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FixedTargetRecovery.posterior`

*Formalization.* `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FixedTargetRecovery.posterior` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every r, label a and original process realization z, posterior(r,a,z) is the real singleton mass at a of condDistrib(target,pastWord(r),J) evaluated at the actual past word.

**Theorem 1.4 (Same-law geometric MAP and Dirac limits).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FixedTargetRecovery.actual_map_recovery`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FixedTargetRecovery.actual_map_recovery` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On exactly the original J, every radius-r fixed-Q0 MAP error is at most ofReal((5/2)*rho^(r/2)), and these MAP estimates are almost surely eventually equal to Q0. For each of the six labels a, the actual target indicator has an almost-everywhere strongly measurable version in the supremum of the raw past fields, and its native posterior coordinate converges almost surely to that indicator. For every measurable seed space U and every probability measure nu, conditional expectations under the actual product-law completion and completed enlarged pastFiltration(nu,r) converge almost surely to the lifted target indicator. The seed is independent of the entire hidden/output process because the measure is J.prod(nu). The proof uses summable actual errors, Borel-Cantelli, measurable eventual-equality events and actual conditional-expectation martingale convergence. The target remains at time zero at every radius.

**Definition 1.5 (Almost-surely finite observable returns).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FixedTargetRecovery.admissible`

*Formalization.* `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FixedTargetRecovery.admissible` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For any measurable seed law nu, an arbitrary WithTop Nat-valued return map tau and arbitrary six-label returned map A are admissible when every finite return-label event is measurable in pastFiltration(nu,r), completed under J.prod(nu), and tau is finite almost surely. Nonterminating values remain in the domain.

**Definition 1.6 (The actual stopped-error infimum).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FixedTargetRecovery.stoppingErrorInf`

*Formalization.* `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FixedTargetRecovery.stoppingErrorInf` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each measurable seed law nu, stoppingErrorInf is the ENNReal infimum of J.prod(nu)(A differs from the fixed Q0) over all return maps tau, all returned maps A, and proofs of admissible(nu,tau,A).

**Theorem 1.7 (Zero error infimum without a finite zero-error return).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FixedTargetRecovery.actual_zero_unattained_infimum`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FixedTargetRecovery.actual_zero_unattained_infimum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every measurable seed space and probability nu, stoppingErrorInf(nu) is zero. Every admissible tau,A is a genuine stopping time for the actual completed enlarged filtration and has strictly positive actual product-law error. Every finite-radius actual MAP error under J is also strictly positive. The proof applies zero_error_iff_dirac_hitting to the actual native posterior vector on the completed common product measure. The native vectors are normalized and measurable, actual_completed_posterior supplies their conditional-expectation identities, and exact finite-past support excludes every finite Dirac hit. Deterministic finite MAP returns and the geometric bound approach zero error, so no radius-independent positive error floor follows.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FixedTargetRecovery.actual_map_recovery`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FixedTargetRecovery.actual_zero_unattained_infimum`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FixedTargetRecovery.admissible`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FixedTargetRecovery.fixedMAP`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FixedTargetRecovery.pastInformation`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FixedTargetRecovery.posterior`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FixedTargetRecovery.stoppingErrorInf`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FinitePosteriorDiracStopping](FinitePosteriorDiracStopping.md)
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FixedTargetStopping](FixedTargetStopping.md)
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/TwelveStateTail](TwelveStateTail.md)

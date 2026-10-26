# Critical renewal sources and counted table

## Abstract

Exact renewal laws and the literal capped table.

**Theorem 1.1 (Exact gap and equilibrium laws).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalTable.source_laws`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalTable.source_laws` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a natural r at least one, a positive real c, and s>0. The two shapes at every positive integer k are k^(2r-1) and k^(2r-1)+c k^(r-1). Their weights multiply these shapes by exp(-s k); both weights and densities are exactly zero at k=0. The normalizer is the sum over positive k. Every normalizer and positive-index density is strictly positive, both densities sum to one, and every fixed polynomial moment is finite.

The density moments define mu=1+E K and beta=(E K^2+E K)/(2 mu). The tail S(u) sums the density over k>=u. Both S(0) and S(1) equal one, the sum of all tails is mu, and the equilibrium forward-wait mass is S(u)/mu for every natural u, including zero. This mass sums to one, its first moment is finite, and its mean is beta. The definitions gapLaw and waitLaw give the corresponding probability mass functions. The theorem also proves integrability and the actual measure integrals for every gap moment and for the equilibrium wait.

For the equilibrium identities, a mass at gap k occurs once at each forward wait 0 through k. Summing these contributions gives (k+1) times its mass. Weighting each occurrence by its wait gives k(k+1)/2 times that same mass. Absolute summability follows from the polynomial geometric moments before interchanging the sums.

Writing R_m(s) for the positive-index polynomial exponential sum and g=R_(r-1)/R_(2r-1), the exact pair identity is Z_1=(1+c g)Z_0. At every k>=1 the signed density difference is c[k^(r-1)-g k^(2r-1)] exp(-s k)/Z_1. The subtracted normalizer correction remains in this identity.

**Theorem 1.2 (One neighborhood for both source labels).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalTable.common_scalar_neighborhood`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalTable.common_scalar_neighborhood` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each fixed r>=1 and c>0 there are sStar in (0,1) and positive zMinus,zPlus,G,Cmu,Cbeta such that, whenever 0<s<sStar, both normalizers lie between zMinus/s^(2r) and zPlus/s^(2r), both cycle means are at most Cmu/s, and both 1+beta values are at most Cbeta/s. On the same neighborhood g<=G s^r. These constants are chosen before s and before every later phase cap.

The polynomial geometric sum formula expresses the full natural-index sum using Stirling numbers of the second kind. Its zero-index term is removed explicitly, including when the exponent is zero. Clearing the denominator (1-exp(-s))^(m+1) leaves a finite polynomial whose value at exp(-s)=1 is m!. The derivative of 1-exp(-s) at zero is one, so s^(m+1)R_m(s) tends to m! from the positive side.

For both shapes, every scaled raw moment has the same factorial limit as its leading monomial: the added term has a factor s^r and tends to zero. The source mean, equilibrium mean and g are ratios of these scaled quantities with positive limiting denominators. The finite collection of strict bounds for both labels has a common positive neighborhood. No moment estimate is an additional source assumption.

**Theorem 1.3 (The actual capped zero row).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalTable.phase_coin_row`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalTable.phase_coin_row` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural cap J and phase z in Fin(J+1), mapping a Bernoulli coin with success probability 2^(-(z+1)) through Phase.step z gives exactly GeometricPhaseOccupation.finiteCappedRow J z. Live index z denotes source phase z+1. The last index J is dead; both fresh outcomes there have the same destination.

The deterministic phase step stays on false and advances to min(z+1,J) on true. This includes J=0 and all finite phases.

**Theorem 1.4 (Every bit row is a fresh coin transition).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalTable.fresh_row`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalTable.fresh_row` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive natural H, natural J, immutable Tick J, counted state s and Boolean input bit x, the distribution of next(s,x,b), when b has coin(s,x), is exactly row(s,x).

The complete state carrier is one wait, two Boolean labels, and every integer evidence value strictly between -H and H paired with Fin(J+1). Wait holds on zero and enters evidence zero and phase zero on one. Both label rows fix their label. Active zero rows use the capped phase row at fixed evidence. Active tick rows round by lower(z)+b and go directly through target. target emits label one at or above H, label zero at or below -H, and otherwise retains the new evidence at phase zero. The order of these cases is explicit. No pending phase is needed.

The coin outcome is consumed by one transition. Its retained consequence is only the successor in the counted carrier. The table depends on no source label, time, history, gap length or external register. A tick following zero zeros is a fully specified row.

**Theorem 1.5 (The complete actual-gap row).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalTable.complete_gap_row`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalTable.complete_gap_row` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive H, natural J, immutable Tick J, interior evidence e and natural duration k, wordLaw from (e,first) along exactly k zeros and one closing tick is the capped phase law at k, followed by that same phase's tick coin and target(e+lower(z)+b). The duration k=0 is included.

wordLaw samples a new row coin for every consecutive input bit and applies the deterministic counted-state successor. No zero after phase death is omitted. Capped phase death preserves the evidence while zeros continue to be read.

**Theorem 1.6 (Duration and mark remain joint).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalTable.random_gap_row`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalTable.random_gap_row` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any probability mass function f on natural durations, the f-mixture of the literal complete-gap rows at an interior evidence e is the pushforward of pairLaw f t through (k,u) mapped to target(e+u).

pairLaw first draws k with law f, then the capped phase after its k zeros, and finally the tick coin at that phase. Its second coordinate is the integer increment lower(z)+b. The increment is not assumed independent of its own duration.

**Theorem 1.7 (The entire listed carrier).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalTable.full_state_count`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalTable.full_state_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural J and positive natural H, the cardinality of State H J is exactly 3+(2H-1)(J+1). All interior integer evidence values and all phases count; no reachability or positive-probability restriction is imposed.

The three distinguished states are the wait and two internally emitted labels. The evidence interval has 2H-1 integers and the capped phase carrier has J+1 elements. The real choice H=ceil(A/delta) is a separate numerical specialization of this exact natural-H identity.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalTable.common_scalar_neighborhood`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalTable.complete_gap_row`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalTable.fresh_row`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalTable.full_state_count`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalTable.phase_coin_row`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalTable.random_gap_row`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalTable.source_laws`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/GeometricPhaseOccupation](../GeometricPhaseOccupation.md)

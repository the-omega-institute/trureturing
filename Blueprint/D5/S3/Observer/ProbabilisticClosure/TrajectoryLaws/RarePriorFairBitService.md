# RarePriorFairBitService

## Abstract

RarePriorFairBitService

The service holds a threshold tag, PC, Fin 7 position, Fin 128 candidate and one output bit. Reset clears the registers. Only a bit instruction reads fresh randomness. Seven sequential fair bits produce a binary candidate; comparison accepts 0 through 99 and tests the fixed thresholds 40, 90 and 1. Rejection clears both candidate and position and returns to reset without retaining a retry number.

The packet law is the product of seven fair Bernoulli bit measures. Independent packet streams retain all infinite paths. Rejection has probability 28/128=7/32, so finite rejection survival is (7/32) to the m. Actual first-return alpha cylinders are disjoint; summing their product masses gives 2/5, 9/10 and 1/100. The service trajectory either remains at reset after a rejected prefix or retains its first accepted result. Its eventual alpha output event equals the union of these first-return cylinders.

A paused bit instruction consumes precisely its remaining bits. Its first partial trial either returns or resets; every subsequent rejected trial is a fresh canonical packet. The actual never-return event is contained in the shifted infinite rejection event of measure zero. This argument covers every service microstate, including comparison, partial candidates, reset and already returned states. Individual transitions use only weights 0, 1/2 and 1.

**Theorem 1.1 (seven bit candidate).**

$$\forall ( \operatorname{t} : \operatorname{Threshold} ) , ( \forall ( \operatorname{p} : \operatorname{Packet} ) , ( \operatorname{collectPacket} \operatorname{t} \operatorname{p} = \langle \operatorname{t} , . \operatorname{compare} , 6 , \operatorname{packetEquiv} \operatorname{p} , 0 \rangle ) )$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorFairBitService.seven_bit_candidate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Successive binary shifts assemble the seven fresh bits into the addressed Fin 128 candidate and enter comparison.

**Theorem 1.2 (packet transaction).**

$$\forall ( \operatorname{t} : \operatorname{Threshold} ) , ( \forall ( \operatorname{p} : \operatorname{Packet} ) , ( \operatorname{microStep} ( \operatorname{collectPacket} \operatorname{t} \operatorname{p} ) 0 = \operatorname{if} ( \operatorname{packetEquiv} \operatorname{p} ) . \operatorname{val} < 100 \operatorname{then} \langle \operatorname{t} , . \operatorname{returned} , 6 , \operatorname{packetEquiv} \operatorname{p} , \operatorname{if} ( \operatorname{packetEquiv} \operatorname{p} ) . \operatorname{val} < ( \operatorname{threshold} \operatorname{t} ) . \operatorname{val} \operatorname{then} 0 \operatorname{else} 1 \rangle \operatorname{else} \operatorname{entry} \operatorname{t} ) )$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorFairBitService.packet_transaction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Comparison accepts candidates below 100, returns the threshold color, or clears the candidate and position and enters reset.

**Theorem 1.3 (microstep weights).**

$$\forall ( \operatorname{s} \operatorname{q} : \operatorname{Service} ) , ( \operatorname{microWeight} \operatorname{s} \operatorname{q} = 0 \lor \operatorname{microWeight} \operatorname{s} \operatorname{q} = 1 / 2 \lor \operatorname{microWeight} \operatorname{s} \operatorname{q} = 1 )$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorFairBitService.microstep_weights` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A bit step is the sum of two half-weight deterministic images; every other instruction has a single unit-weight image.

**Theorem 1.4 (fair packet mass).**

$$\forall ( \operatorname{p} : \operatorname{Packet} ) , ( \operatorname{wordMass} \operatorname{fairParameter} ( \operatorname{packetBits} \operatorname{p} ) = 1 / 128 )$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorFairBitService.fair_packet_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The seven independent fair singleton masses multiply to one over 128 for every packet.

**Theorem 1.5 (survival geometric).**

$$\forall ( \operatorname{m} : \mathbb{N} ) , ( \operatorname{survivalMass} \operatorname{m} = ( 7 / 32 ) ^{\operatorname{m}} )$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorFairBitService.survival_geometric` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exactly 28 of the 128 packet addresses reject. Iterating the rejection recurrence multiplies survival by seven over 32.

**Theorem 1.6 (exact service law).**

$$\operatorname{returnedAlphaMass} . \operatorname{ordinary} = 2 / 5 \land \operatorname{returnedAlphaMass} . \operatorname{high} = 9 / 10 \land \operatorname{returnedAlphaMass} . \operatorname{low} = 1 / 100 \land \operatorname{Tendsto} \operatorname{survivalMass} \operatorname{atTop} ( \operatorname{nhds} 0 )$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorFairBitService.exact_service_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Summing the geometric first-return masses gives the three threshold fractions. The rejection survival tends to zero.

**Theorem 1.7 (actual survival probability).**

$$\forall ( \operatorname{m} : \mathbb{N} ) , ( \operatorname{packetStreamLaw} ( \operatorname{survives} \operatorname{m} ) = ( 7 / 32 : \mathbb{R}_{\geq 0}^{\infty} ) ^{\operatorname{m}} )$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorFairBitService.actual_survival_probability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Independent stream cylinders requiring m rejected packets have measure equal to the mth power of seven over 32.

**Theorem 1.8 (almost sure service return).**

$$\operatorname{packetStreamLaw} ( \operatorname{iInter} \operatorname{m} : \mathbb{N} , \operatorname{survives} \operatorname{m} ) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorFairBitService.almost_sure_service_return` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Continuity of measure for the decreasing rejection cylinders gives zero measure to infinite rejection.

**Theorem 1.9 (actual service output law).**

$$\forall ( \operatorname{t} : \operatorname{Threshold} ) , ( \operatorname{packetStreamLaw} ( \operatorname{iUnion} \operatorname{m} : \mathbb{N} , \operatorname{alphaReturnEvent} \operatorname{t} \operatorname{m} ) = \operatorname{ENNReal} . \operatorname{ofReal} ( \operatorname{returnedAlphaMass} \operatorname{t} ) )$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorFairBitService.actual_service_output_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Disjoint first-alpha-return cylinders have the computed product masses, whose countable sum is the returned alpha mass.

**Theorem 1.10 (every microstate returns).**

$$\forall ( \operatorname{s} : \operatorname{Service} ) , ( \operatorname{packetStreamLaw} ( \operatorname{neverReturns} \operatorname{s} ) = 0 )$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorFairBitService.every_microstate_returns` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first partial trial either returns or resets. Any subsequent nonreturning trajectory lies in a shifted infinite rejection event of measure zero.

**Theorem 1.11 (rational service realization).**

$$\forall ( \operatorname{t} : \operatorname{Threshold} ) , ( \operatorname{packetStreamLaw} ( \operatorname{iUnion} \operatorname{m} : \mathbb{N} , \operatorname{alphaReturnEvent} \operatorname{t} \operatorname{m} ) = \operatorname{ENNReal} . \operatorname{ofReal} ( ( \operatorname{threshold} \operatorname{t} ) . \operatorname{val} / ( 100 : \mathbb{R} ) ) \land ( \forall \operatorname{s} \operatorname{q} : \operatorname{Service} , \operatorname{microWeight} \operatorname{s} \operatorname{q} = 0 \lor \operatorname{microWeight} \operatorname{s} \operatorname{q} = 1 / 2 \lor \operatorname{microWeight} \operatorname{s} \operatorname{q} = 1 ) \land ( \forall \operatorname{s} : \operatorname{Service} , \operatorname{packetStreamLaw} ( \operatorname{neverReturns} \operatorname{s} ) = 0 ) )$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorFairBitService.rational_service_realization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The measured first-return law, allowed microstep weights and almost-sure return hold together for the explicit service.

**Theorem 1.12 (operational service realization).**

$$\forall ( \operatorname{t} : \operatorname{Threshold} ) , ( \operatorname{alphaOutputEvent} \operatorname{t} = \operatorname{iUnion} \operatorname{m} : \mathbb{N} , \operatorname{alphaReturnEvent} \operatorname{t} \operatorname{m} \land \operatorname{packetStreamLaw} ( \operatorname{alphaOutputEvent} \operatorname{t} ) = \operatorname{ENNReal} . \operatorname{ofReal} ( ( \operatorname{threshold} \operatorname{t} ) . \operatorname{val} / ( 100 : \mathbb{R} ) ) \land ( \forall \operatorname{s} \operatorname{q} : \operatorname{Service} , \operatorname{microWeight} \operatorname{s} \operatorname{q} = 0 \lor \operatorname{microWeight} \operatorname{s} \operatorname{q} = 1 / 2 \lor \operatorname{microWeight} \operatorname{s} \operatorname{q} = 1 ) \land ( \forall \operatorname{s} : \operatorname{Service} , \operatorname{packetStreamLaw} ( \operatorname{neverReturns} \operatorname{s} ) = 0 ) \land \operatorname{packetStreamLaw} ( \operatorname{iInter} \operatorname{m} : \mathbb{N} , \operatorname{survives} \operatorname{m} ) = 0 )$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorFairBitService.operational_service_realization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The canonical trajectory retains the first accepted result. Its eventual alpha output event equals the cylinder union, transferring the exact probability calculation to operational output.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorFairBitService.actual_service_output_law`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorFairBitService.actual_survival_probability`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorFairBitService.almost_sure_service_return`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorFairBitService.every_microstate_returns`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorFairBitService.exact_service_law`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorFairBitService.fair_packet_mass`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorFairBitService.microstep_weights`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorFairBitService.operational_service_realization`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorFairBitService.packet_transaction`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorFairBitService.rational_service_realization`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorFairBitService.seven_bit_candidate`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorFairBitService.survival_geometric`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorFiniteMonitor](RarePriorFiniteMonitor.md)

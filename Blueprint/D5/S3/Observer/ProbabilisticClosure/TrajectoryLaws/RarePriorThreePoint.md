# RarePriorThreePoint

## Abstract

RarePriorThreePoint

The normalized prior has rational weights at native depths 1, 2 and 3, whose source rates are 1/3, 2/5 and 3/8. Every legal short history uses the same selected prior. The exact same-history endpoint posterior identifies the zero-rare posterior, yielding a perturbation bound for the complete unbounded original record target. Long native histories activate the fixed monitor and concentrate on depth 3. Law error is the complete-record TV of historyGenerated and fullTarget. Configuration error averages that TV under the actual retained row before the supremum. phaseLawRisk and phaseConfRisk take the original PhaseHistory domain; shortLawRisk and shortConfRisk restrict its paid Reads to H. Pure actual rows prove equality, and all these ENNReal risks are bounded by 1 before toReal. Short-cap risk differs from the zero-rare risk by at most 1/1000. The full first-alpha cylinder gives phase-p risk at least 21/40. RarePriorAbsoluteRisk.all_history_absolute_risks bounds both absolute native zero-rare law and configuration risks on all original phase histories by 253/500 in p and 2/5 in beta. Original radius identification, Phi, charged full-machine realization and the uniform cutoff refutation U remain open.

**Theorem 1.1 (every short history).**

$$\forall ( \operatorname{H} : \operatorname{Nat} ) , ( 0 < ( \operatorname{shortParameter} \operatorname{H} ) . \operatorname{value} \land ( \forall \operatorname{k} : \operatorname{Depth} , \operatorname{prior} ( \operatorname{shortParameter} \operatorname{H} ) \operatorname{k} = \operatorname{weight} ( \operatorname{shortParameter} \operatorname{H} ) \operatorname{k} ) \land ( \forall ( \operatorname{ops} : \operatorname{List} \operatorname{Operation} ) ( \operatorname{c} : \operatorname{AcquiredNativeState} ) ( \operatorname{hc} : \operatorname{run} \operatorname{ops} = \operatorname{some} \operatorname{c} ) , ( \operatorname{readLetters} \operatorname{ops} ) . \operatorname{length} \leq \operatorname{H} \Rightarrow ( ( \operatorname{posterior} ( \operatorname{prior} ( \operatorname{shortParameter} \operatorname{H} ) ) \operatorname{ops} \operatorname{c} \operatorname{hc} ) \operatorname{depthThree} ) . \operatorname{toReal} < 1 / 1000 ) )$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorThreePoint.every_short_history` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The statement retains the complete original telescope and conditions.

**Theorem 1.2 (every short complete target).**

$$\forall ( \operatorname{H} : \operatorname{Nat} ) , ( \forall ( \operatorname{ops} : \operatorname{List} \operatorname{Operation} ) , ( \forall ( \operatorname{c} : \operatorname{AcquiredNativeState} ) , ( \forall ( \operatorname{hc} : \operatorname{run} \operatorname{ops} = \operatorname{some} \operatorname{c} ) , ( ( ( \operatorname{readLetters} \operatorname{ops} ) . \operatorname{length} \leq \operatorname{H} ) \Rightarrow ( ( \forall \operatorname{k} : \operatorname{Depth} , ( \operatorname{posterior} ( \operatorname{prior} ( \operatorname{shortParameter} \operatorname{H} ) ) \operatorname{ops} \operatorname{c} \operatorname{hc} ) \operatorname{k} = \operatorname{ENNReal} . \operatorname{ofReal} ( 1 - ( ( \operatorname{posterior} ( \operatorname{prior} ( \operatorname{shortParameter} \operatorname{H} ) ) \operatorname{ops} \operatorname{c} \operatorname{hc} ) \operatorname{depthThree} ) . \operatorname{toReal} ) * ( \operatorname{posterior} \operatorname{muZero} \operatorname{ops} \operatorname{c} \operatorname{hc} ) \operatorname{k} + \operatorname{ENNReal} . \operatorname{ofReal} ( ( \operatorname{posterior} ( \operatorname{prior} ( \operatorname{shortParameter} \operatorname{H} ) ) \operatorname{ops} \operatorname{c} \operatorname{hc} ) \operatorname{depthThree} ) . \operatorname{toReal} * ( \operatorname{PMF} . \operatorname{pure} \operatorname{depthThree} ) \operatorname{k} ) \land \operatorname{measurableTotalVariation} ( \operatorname{NativeObserverJointLaw} . \operatorname{fullTarget} \operatorname{RarePriorFullFields} . \operatorname{actualObserver} ( \operatorname{prior} ( \operatorname{shortParameter} \operatorname{H} ) ) \operatorname{ops} \operatorname{c} ) ( \operatorname{NativeObserverJointLaw} . \operatorname{fullTarget} \operatorname{RarePriorFullFields} . \operatorname{actualObserver} \operatorname{muZero} \operatorname{ops} \operatorname{c} ) < \operatorname{ENNReal} . \operatorname{ofReal} ( 1 / 1000 ) \land \exists \operatorname{z} : \operatorname{Runtime} , \operatorname{runtimeRun} \operatorname{ops} = \operatorname{some} \operatorname{z} \land \operatorname{z} . \operatorname{fields} = \operatorname{c} . \operatorname{source} . \operatorname{finiteFields} \land \operatorname{NativeObserverJointLaw} . \operatorname{row} \operatorname{RarePriorFullFields} . \operatorname{actualObserver} \operatorname{ops} = \operatorname{PMF} . \operatorname{pure} \operatorname{z} \land \operatorname{RarePriorGeneratedLaw} . \operatorname{historyGenerated} \operatorname{ops} = \operatorname{RarePriorGeneratedLaw} . \operatorname{decoder} \operatorname{z} \land \forall ( \operatorname{op} : \operatorname{Operation} ) ( \operatorname{d} : \operatorname{AcquiredNativeState} ) , \operatorname{nativeStep} \operatorname{c} \operatorname{op} = \operatorname{some} \operatorname{d} \Rightarrow \operatorname{NativeObserverJointLaw} . \operatorname{row} \operatorname{RarePriorFullFields} . \operatorname{actualObserver} ( \operatorname{ops} + + [ \operatorname{op} ] ) = \operatorname{RarePriorFullFields} . \operatorname{actualUpdate} \operatorname{op} \operatorname{z} \land ( \operatorname{ProbabilityTheory} . \operatorname{cond} ( \operatorname{RarePriorGeneratedLaw} . \operatorname{historyGenerated} \operatorname{ops} ) \{ \operatorname{t} | \operatorname{RarePriorGeneratedLaw} . \operatorname{firstOperation} \operatorname{t} = \operatorname{some} \operatorname{op} \} ) . \operatorname{map} \operatorname{NativeFullResidual} . \operatorname{deleteBlock} = \operatorname{RarePriorGeneratedLaw} . \operatorname{historyGenerated} ( \operatorname{ops} + + [ \operatorname{op} ] ) ) ) ) ) )$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorThreePoint.every_short_complete_target` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The statement retains the complete original telescope and conditions.

**Theorem 1.3 (long history concentration).**

$$\forall ( \operatorname{t} : \operatorname{Parameter} ) , ( ( 0 < \operatorname{t} . \operatorname{value} ) \Rightarrow ( ( \forall \operatorname{n} : \operatorname{Nat} , \operatorname{run} ( \operatorname{longHistory} \operatorname{n} ) = \operatorname{some} ( \operatorname{longState} \operatorname{n} ) \land 0 < \operatorname{normalizer} ( \operatorname{prior} \operatorname{t} ) ( \operatorname{longHistory} \operatorname{n} ) ) \land ( \forall \operatorname{n} : \operatorname{Nat} , 375 \leq \operatorname{n} \Rightarrow \operatorname{runtimeRun} ( \operatorname{longHistory} \operatorname{n} ) = \operatorname{some} \langle \operatorname{latchedFields} , . \operatorname{accepted} , . \operatorname{g} \rangle ) \land \operatorname{realMass} \operatorname{depthOne} \operatorname{blockWord} < \operatorname{realMass} \operatorname{depthThree} \operatorname{blockWord} \land \operatorname{realMass} \operatorname{depthTwo} \operatorname{blockWord} < \operatorname{realMass} \operatorname{depthThree} \operatorname{blockWord} \land \operatorname{Tendsto} ( \operatorname{fun} \operatorname{n} \mapsto ( ( \operatorname{posterior} ( \operatorname{prior} \operatorname{t} ) ( \operatorname{longHistory} \operatorname{n} ) ( \operatorname{longState} \operatorname{n} ) ( \operatorname{long}_{\operatorname{run}} \operatorname{n} ) ) \operatorname{depthThree} ) . \operatorname{toReal} ) \operatorname{atTop} ( \operatorname{nhds} 1 ) ) )$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorThreePoint.long_history_concentration` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The statement retains the complete original telescope and conditions.

**Theorem 1.4 (long endpoint calibration).**

$$\forall ( \operatorname{n} : \operatorname{Nat} ) , ( ( 375 \leq \operatorname{n} ) \Rightarrow ( \operatorname{realMass} \operatorname{depthTwo} ( \operatorname{blocks} \operatorname{n} + + \operatorname{latchWord} ) / \operatorname{realMass} \operatorname{depthOne} ( \operatorname{blocks} \operatorname{n} + + \operatorname{latchWord} ) = ( 27 / 25 : \operatorname{Real} ) ^{3}* ( 1594323 / 1562500 : \operatorname{Real} ) ^{(2 * \operatorname{n} )} \land 16 < \operatorname{realMass} \operatorname{depthTwo} ( \operatorname{blocks} \operatorname{n} + + \operatorname{latchWord} ) / \operatorname{realMass} \operatorname{depthOne} ( \operatorname{blocks} \operatorname{n} + + \operatorname{latchWord} ) \land 79 / 200 < ( ( \operatorname{posterior} \operatorname{muZero} ( \operatorname{longHistory} \operatorname{n} ) ( \operatorname{longState} \operatorname{n} ) ( \operatorname{long}_{\operatorname{run}} \operatorname{n} ) ) \operatorname{depthOne} ) . \operatorname{toReal} / 3 + ( ( \operatorname{posterior} \operatorname{muZero} ( \operatorname{longHistory} \operatorname{n} ) ( \operatorname{longState} \operatorname{n} ) ( \operatorname{long}_{\operatorname{run}} \operatorname{n} ) ) \operatorname{depthTwo} ) . \operatorname{toReal} * ( 2 / 5 ) \land \operatorname{RarePriorReferenceScalar} . \operatorname{tStar} + 47 / 100 < 21 / 40 - ( 1116529 / 22781250 : \operatorname{Real} ) \land ( \forall ( \operatorname{t} : \operatorname{Parameter} ) , 0 < \operatorname{t} . \operatorname{value} \Rightarrow \operatorname{Tendsto} ( \operatorname{fun} \operatorname{m} \mapsto ( ( \operatorname{posterior} ( \operatorname{prior} \operatorname{t} ) ( \operatorname{longHistory} \operatorname{m} ) ( \operatorname{longState} \operatorname{m} ) ( \operatorname{long}_{\operatorname{run}} \operatorname{m} ) ) \operatorname{depthThree} ) . \operatorname{toReal} ) \operatorname{atTop} ( \operatorname{nhds} 1 ) ) ) )$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorThreePoint.long_endpoint_calibration` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The statement retains the complete original telescope and conditions.

**Theorem 1.5 (complete record risk bridges).**

$$\forall ( \operatorname{t} : \operatorname{Parameter} ) , ( ( 0 < \operatorname{t} . \operatorname{value} ) \Rightarrow ( ( \forall ( \operatorname{mu} : \operatorname{PMF} \operatorname{Depth} ) ( \operatorname{h} : \operatorname{List} \operatorname{Operation} ) ( \operatorname{c} : \operatorname{AcquiredNativeState} ) , \operatorname{run} \operatorname{h} = \operatorname{some} \operatorname{c} \Rightarrow \operatorname{confError} \operatorname{mu} \operatorname{h} \operatorname{c} = \operatorname{lawError} \operatorname{mu} \operatorname{h} \operatorname{c} \land \operatorname{lawError} \operatorname{mu} \operatorname{h} \operatorname{c} \leq 1 ) \land ( \forall ( \operatorname{mu} : \operatorname{PMF} \operatorname{Depth} ) ( \operatorname{s} : \operatorname{ActivePhase} ) , \operatorname{phaseConfRisk} \operatorname{mu} \operatorname{s} = \operatorname{phaseLawRisk} \operatorname{mu} \operatorname{s} \land \operatorname{phaseLawRisk} \operatorname{mu} \operatorname{s} \leq 1 \land \forall \operatorname{H} : \operatorname{Nat} , \operatorname{shortConfRisk} \operatorname{mu} \operatorname{s} \operatorname{H} = \operatorname{shortLawRisk} \operatorname{mu} \operatorname{s} \operatorname{H} \land \operatorname{shortLawRisk} \operatorname{mu} \operatorname{s} \operatorname{H} \leq 1 ) \land ( \forall ( \operatorname{s} : \operatorname{ActivePhase} ) ( \operatorname{H} : \operatorname{Nat} ) , ( \operatorname{shortLawRisk} ( \operatorname{prior} ( \operatorname{shortParameter} \operatorname{H} ) ) \operatorname{s} \operatorname{H} ) . \operatorname{toReal} \leq ( \operatorname{shortLawRisk} \operatorname{muZero} \operatorname{s} \operatorname{H} ) . \operatorname{toReal} + 1 / 1000 ) \land ( \forall \operatorname{n} : \operatorname{Nat} , 375 \leq \operatorname{n} \Rightarrow \operatorname{RarePriorGeneratedLaw} . \operatorname{historyGenerated} ( \operatorname{longHistory} \operatorname{n} ) \operatorname{firstAlpha} = \operatorname{ENNReal} . \operatorname{ofReal} ( 9 / 10 ) \land - 1 / 10 + ( 5 / 8 ) * ( ( \operatorname{posterior} ( \operatorname{prior} \operatorname{t} ) ( \operatorname{longHistory} \operatorname{n} ) ( \operatorname{longState} \operatorname{n} ) ( \operatorname{long}_{\operatorname{run}} \operatorname{n} ) ) \operatorname{depthThree} ) . \operatorname{toReal} \leq ( \operatorname{lawError} ( \operatorname{prior} \operatorname{t} ) ( \operatorname{longHistory} \operatorname{n} ) ( \operatorname{longState} \operatorname{n} ) ) . \operatorname{toReal} ) \land 21 / 40 \leq ( \operatorname{phaseLawRisk} ( \operatorname{prior} \operatorname{t} ) . \operatorname{p} ) . \operatorname{toReal} \land \operatorname{RarePriorReferenceScalar} . \operatorname{tStar} + 47 / 100 < ( \operatorname{phaseLawRisk} ( \operatorname{prior} \operatorname{t} ) . \operatorname{p} ) . \operatorname{toReal} - ( 1116529 / 22781250 : \operatorname{Real} ) ) )$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorThreePoint.complete_record_risk_bridges` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The statement retains the complete original telescope and conditions.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorThreePoint.complete_record_risk_bridges`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorThreePoint.every_short_complete_target`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorThreePoint.every_short_history`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorThreePoint.long_endpoint_calibration`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorThreePoint.long_history_concentration`
- Dependency: [D5/S3/Estimation/DataProcessing/MeasurableTotalVariationTriangle](../../../Estimation/DataProcessing/MeasurableTotalVariationTriangle.md)
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorGeneratedLaw](RarePriorGeneratedLaw.md)
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorReferenceScalar](RarePriorReferenceScalar.md)

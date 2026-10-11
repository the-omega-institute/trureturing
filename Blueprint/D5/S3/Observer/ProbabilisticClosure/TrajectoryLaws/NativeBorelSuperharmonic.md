# Signed defect, harmonic limit and sixth-power gain

## Abstract

Superharmonic completion on the acquired chain

F is an arbitrary original boxed CommonFlow. The acquired return chain is C=BA with its original stationary unweighted p marginal, and L has the original (1-u)*v weights. T is normalizedAction, with endpointRate=6/25. The ENNReal threeStepAverage is (g+Tg+T squared g)/3; h is its real value, excess=g.toReal-9/25, and delta=h-(Th).toReal uses signed real subtraction. AE(mu,Q,P) means P holds for mu-almost every Q. qIterateAt(F,Q) denotes the sequence n mapped to qIterate(F,n,Q). CRow and LRow denote the actual acquired rows.

**Theorem 1.1 (h finite).**

$$\forall F: CommonFlow, \forall Q: PDescriptor, \operatorname{threeStepAverage}\left(F, Q\right)\neq top$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelSuperharmonic.h_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All original normalized g iterates are finite, using L <= C and finite endpointRate inverse. Their finite three-step sum is finite. This bound is consumed by Holder, real conversion and stationary cancellation.

**Theorem 1.2 (h global bound).**

$$\forall F: CommonFlow, \forall Q: PDescriptor, \operatorname{threeStepAverage}\left(F, Q\right)\leq10$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelSuperharmonic.h_global_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The global g bound one and normalized iterate bounds (25/6) to the powers one and two bound the finite three-step average by ten. This global bound is consumed by row integrability and stationary localization.

**Theorem 1.3 (sixth le h).**

$$\forall F: CommonFlow, \forall Q: PDescriptor, \operatorname{sixthFunctional}\left(F, Q\right)\leq\operatorname{threeStepAverage}\left(F, Q\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelSuperharmonic.sixth_le_h` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

q is bounded above by the first term of its infimum, namely threeStepAverage. If h is zero, q is zero. Otherwise cancellation gives q to the sixth power divided by h to the fifth power <= h. This bound supplies finite sixth-functional integrals.

**Theorem 1.4 (sixth measurable).**

$$\forall F: CommonFlow, \operatorname{Measurable}\left(\operatorname{sixthFunctional}\left(F\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelSuperharmonic.sixth_measurable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Countable-infimum measurability and measurable finite powers and division give measurability of the actual sixth functional. This is consumed by Holder and the stationary integral identity.

**Theorem 1.5 (common flow signed h).**

$$\forall F: CommonFlow, (\operatorname{Measurable}\left(\operatorname{descriptorTVBorel}\left(p\right), BorelR, \operatorname{h}\left(F\right)\right) \land \operatorname{AE}\left(\operatorname{nuP}\left(F\right), Q, (\frac{3}{25}\leq\operatorname{h}\left(F, Q\right) \land \operatorname{h}\left(F, Q\right)\leq\frac{1}{2} \land 0\leq\operatorname{excess}\left(Q\right) \land \operatorname{delta}\left(F, Q\right)=\frac{(\operatorname{toReal}\left(\operatorname{g}\left(Q\right)\right)-\operatorname{toReal}\left(\operatorname{normalizedIterate}\left(F, g, 3, Q\right)\right))}{3} \land \frac{\operatorname{excess}\left(Q\right)}{3}\leq\operatorname{delta}\left(F, Q\right) \land \operatorname{normalizedAction}\left(F, \operatorname{threeStepAverage}\left(F\right), Q\right)\leq\operatorname{threeStepAverage}\left(F, Q\right))\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelSuperharmonic.common_flow_signed_h` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

h is measurable for the actual TV-Borel sigma algebra on the exact p descriptor. The original three-step upper endpoint box supplies the signed defect. Finite row domination makes every normalized g iterate finite, so conversion to real values preserves the signed identity. The bound h <= 1/2 follows from g <= 4/9 and T <= (10/9) C for the first two iterates. A global bound ten ensures finite row integrals.

**Theorem 1.6 (common flow q limit).**

$$\forall F: CommonFlow, (\operatorname{Measurable}\left(\operatorname{q}\left(F\right)\right) \land \operatorname{AE}\left(\operatorname{nuP}\left(F\right), Q, (\operatorname{Antitone}\left(\operatorname{qIterateAt}\left(F, Q\right)\right) \land \operatorname{Tendsto}\left(\operatorname{qIterateAt}\left(F, Q\right), atTop, \operatorname{Nhds}\left(\operatorname{q}\left(F, Q\right)\right)\right) \land \operatorname{q}\left(F, Q\right)\leq\operatorname{threeStepAverage}\left(F, Q\right) \land \operatorname{normalizedAction}\left(F, \operatorname{q}\left(F\right), Q\right)=\operatorname{q}\left(F, Q\right))\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelSuperharmonic.common_flow_q_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

qIterate(F,n) is T to the power n applied to the same threeStepAverage, and q is its infimum over all natural n. The initial decrease follows from the signed defect. Stationarity of C transports subsequent conull inequalities to acquired rows, and L <= C transfers them to weighted rows. Decreasing monotone convergence applies because the first row integral is finite. Dropping the first term leaves the infimum unchanged.

**Theorem 1.7 (common flow sixth power gain).**

$$\forall F: CommonFlow, \operatorname{AE}\left(\operatorname{nuP}\left(F\right), Q, \operatorname{sixthFunctional}\left(F, Q\right) \cdot \operatorname{ofReal}\left((1+\frac{10 \cdot \operatorname{excess}\left(Q\right)}{3})\right)\leq\operatorname{normalizedAction}\left(F, \operatorname{sixthFunctional}\left(F\right), Q\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelSuperharmonic.common_flow_sixth_power_gain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

sixthFunctional is q to the sixth power divided by threeStepAverage to the fifth power, on the same actual flow. Weighted Holder with exponents 1/6 and 5/6, followed by Tq=q, gives q to the sixth power <= TF times (Th) to the fifth power. The signed defect and h <= 1/2 yield the displayed multiplicative gain. Positive h and finite row bounds justify division and conversion to reals.

**Theorem 1.8 (common flow unweighted gain).**

$$\forall F: CommonFlow, \operatorname{AE}\left(\operatorname{nuP}\left(F\right), Q, (\operatorname{smul}\left(\operatorname{inv}\left(endpointRate\right), \operatorname{LRow}\left(F, Q\right)\right)\leq\operatorname{smul}\left(\operatorname{ofReal}\left((1+\frac{25 \cdot \operatorname{excess}\left(Q\right)}{9})\right), \operatorname{CRow}\left(F, Q\right)\right) \land (\operatorname{sixthFunctional}\left(F, Q\right)+\frac{9}{20} \cdot \operatorname{ofReal}\left(\operatorname{excess}\left(Q\right)\right) \cdot \operatorname{sixthFunctional}\left(F, Q\right))\leq\operatorname{lintegral}\left(\operatorname{CRow}\left(F, Q\right), R, \operatorname{sixthFunctional}\left(F, R\right)\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelSuperharmonic.common_flow_unweighted_gain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The full B completion equation gives g >= (1-u)*(3/5), while v <= 2/5 bounds the actual weighted row. Thus T <= (1+25*excess/9) C on the original marginal. Together with the sixth-power gain and 0 <= excess <= 19/225, this gives CF >= F+(9/20)*excess*F. The two inequalities use the same acquired B and A, and the margin remains unweighted.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelSuperharmonic.common_flow_q_limit`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelSuperharmonic.common_flow_signed_h`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelSuperharmonic.common_flow_sixth_power_gain`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelSuperharmonic.common_flow_unweighted_gain`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelSuperharmonic.h_finite`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelSuperharmonic.h_global_bound`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelSuperharmonic.sixth_le_h`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelSuperharmonic.sixth_measurable`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelInputTests](NativeBorelInputTests.md)

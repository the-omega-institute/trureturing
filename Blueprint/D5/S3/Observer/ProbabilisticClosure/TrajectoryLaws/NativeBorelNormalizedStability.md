# Complete-configuration normalized endpoint stability

## Abstract

Complete-configuration normalized endpoint stability.

The complete ValidTail carrier is countable and retains every finite legal word and infinity. A CountableAtomicMeasurableSpace has countably many points and measurable singletons; ProbabilityMeasureX and SetX refer to that same X. positiveSideOrder(P,R,S) means R{t}<=P{t} for every t in S; negativeSideOrder means P{t}<=R{t} for every t outside S. eventReal is the real measure of the event. Countable singleton summation compares arbitrary measurable events; probability normalization controls the reverse directed difference through the complement. Thus the sign event attains the actual full measurableTotalVariation supremum.

Ep={pAtom(0,1),pAtom(1,1),pAtom(2,1)} and Eb={betaStop,betaAtom(0,1)} are the lower-endpoint-positive events. Native marker-one mass ratios cross strictly after index two at p and after index zero at suspension. Every other finite atom has the reverse order. Native infinity mass is zero; regular_infinity_zero proves each regular descriptor also assigns it zero mass, while it remains a tested coordinate. These finite sign events evaluate the complete normalized laws and are not truncated measures.

The endpoint encoding and signed defect, late and variation are those of NativeBorelSignedAction. fullLossP and fullLossBeta are fullLoss(p,b,Q) and fullLoss(beta,b,W), where fullLoss(s,b,D) is measurableTotalVariation(law(D),native(s,endpoint(b))).toReal. completeLoss is the maximum of the two configuration loss integrals on the original marginals. meanCoordinate is integral coordinate(n,1).toReal dnuP; slack=signR(b)(meanCoordinate-cR(b)zR(b)^n). HR(false)=9839648/2657205 and HR(true)=20723912/5859375.

emissionDefectP=signR(u.toReal-r) and emissionDefectB=signR(v.toReal-r), so both equal the respective absolute emission deviations at the selected endpoint. The full residual identities give defect=(1-r)emissionDefectP+(1-u)B(emissionDefectB), which bounds each nonnegative part. AIntegral is the original A row integral and vReal=v.toReal. variation_control is the signed inequality -cR*variation <= zR*defect, equivalently the lower bound variation >= -(zR/cR)*defect; it does not give an upper bound. The separate signed_predecessor estimate cR*zR^(k+3)*variation <= late(k+4) supplies the upper bound used in the three-step argument.

**Theorem 1.1 (A full countable probability sign event).**

$$\forall X: CountableAtomicMeasurableSpace, \forall P: ProbabilityMeasureX, \forall R: ProbabilityMeasureX, \forall S: SetX, (\operatorname{MeasurableSet}\left(S\right))\Rightarrow(((\operatorname{positiveSideOrder}\left(P, R, S\right))\land(\operatorname{negativeSideOrder}\left(P, R, S\right)))\Rightarrow(\operatorname{measurableTotalVariation}\left(P, R\right)=\operatorname{ofReal}\left(\operatorname{eventReal}\left(P, S\right)-\operatorname{eventReal}\left(R, S\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelNormalizedStability.complete_sign_event` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Split any measurable event into its intersection with S and its difference from S. Countable atom comparison bounds both exchanged pieces. Normalize the probability complements to bound the reverse directed difference. Taking S itself supplies equality at the supremum.

**Theorem 1.2 (The full p loss before integration).**

$$\forall F: CommonFlow, \forall b: Bool, \operatorname{AE}\left(\operatorname{nuP}\left(F\right), Q, \operatorname{fullLossP}\left(b, Q\right)\leq {1+\operatorname{zR}\left(b\right)+{\operatorname{zR}\left(b\right)}^{2}} \cdot {\operatorname{apply}\left(\operatorname{defect}\left(b\right), Q\right)}+{1+\operatorname{zR}\left(b\right)} \cdot {\operatorname{action}\left(F, \operatorname{defect}\left(b\right), Q\right)}+\operatorname{realIterate}\left(F, \operatorname{defect}\left(b\right), 2, Q\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelNormalizedStability.pointwise_p_loss_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete sign-event TV gives fullLossP=defect-late(1)-late(2). The actual first and second signed recurrences and the emission-defect bound imply the displayed pointwise AE inequality. All complete atoms participated in the sign-event comparison and normalization.

**Theorem 1.3 (The full suspended loss before integration).**

$$\forall F: CommonFlow, \forall b: Bool, \operatorname{AE}\left(\operatorname{nuB}\left(F\right), W, \operatorname{fullLossBeta}\left(b, W\right)={1-\operatorname{cR}\left(b\right)} \cdot {\operatorname{emissionDefectB}\left(b, W\right)}+{\operatorname{vReal}\left(W\right)} \cdot {\operatorname{AIntegral}\left(F, \operatorname{defect}\left(b\right), W\right)}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelNormalizedStability.suspended_loss_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complete Eb TV, the original A_coordinate supplier, native event masses and finite real-integral conversion give the exact suspended formula. Unweighted A and B marginal transport then controls its integral on the same pair.

**Theorem 1.4 (Both endpoints and all return indices).**

$$\forall F: CommonFlow, \forall b: Bool, \forall n: Nat, (4\leq n)\Rightarrow(\operatorname{completeLoss}\left(F, b\right)\leq {\operatorname{HR}\left(b\right)} \cdot {\frac{\operatorname{slack}\left(F, b, n\right)}{{\operatorname{cR}\left(b\right)} \cdot {{\operatorname{zR}\left(b\right)}^{n}}}})$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelNormalizedStability.normalized_stability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Phi be the unweighted p mean of defect and M=1+z+z^2+(1+z)(4/15)+(4/15)^2. Both complete configuration loss integrals are at most M Phi; the suspended coefficients 37/30 and 22/15 are bounded by the respective M values 3379/2025 and 9559/5625. Combine this actual complete-law conversion with integrated_three_step and integral late=slack. Positive c and z permit the final division. Exact rational evaluation gives the two stated HR values. No finite support, recurrence, deterministic successor, mixing, commutation or invariant-L premise is introduced.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelNormalizedStability.complete_sign_event`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelNormalizedStability.normalized_stability`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelNormalizedStability.pointwise_p_loss_bound`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelNormalizedStability.suspended_loss_formula`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelSignedAction](NativeBorelSignedAction.md)

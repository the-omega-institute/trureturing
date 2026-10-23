# The literal Sign ring quotient

## Abstract

Literal integral Sign elimination preserves forward time and both inverse maps.

**Theorem 1.1 (The consumed geometric certificate).**

$$\forall q \in Nat,\; \operatorname{sub}\left(\operatorname{power}\left(X, q\right), \operatorname{multiply}\left(\operatorname{sub}\left(X, 1\right), \operatorname{S}\left(q\right)\right)\right) = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResetSignIntegerCyclic.geometric` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This existing all-natural-q certificate is public for ResetIntegralGluing's actual ideal and coefficient-half reconstruction. The proof is reused unchanged and is a consumed helper.

**Theorem 1.2 (The consumed integral sign involution).**

$$\forall q \in Nat,\; \operatorname{multiply}\left(\operatorname{fp}\left(q, \operatorname{W}\left(q\right)\right), \operatorname{fp}\left(q, \operatorname{W}\left(q\right)\right)\right) = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResetSignIntegerCyclic.sign_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original sign certificate supplies the inverse of wUnit in ResetIntegralUnits. Its proof and scope are unchanged.

Sign is Multiplicative Bool, oddTau is ofAdd true, and the coefficient ring R is literally MonoidAlgebra Int Sign. Its resetLabel is single oddTau 1 from ResetNativeOddObstruction. Put S(q)=sum over k<q of X^k, F(q)=X^(2q)-S(q)^2, and W(q)=S(q)-(X-1)*X^q. QP(q) is the accepted FiniteCompanionCyclicModule.CyclicQ at R and resetLabel, hence R[X]/(P), where P=X^q-C(resetLabel)*S(q). QF(q) is Int[X]/(F). pp and fp are their canonical quotient ring maps; inclusion maps integer coefficients canonically into R. No rational sign splitting, rank argument, or history equivariance assumption is used.

**Theorem 1.3 (Actual inverse quotient maps and generator images).**

$$\forall q \in Nat,\; \operatorname{compose}\left(\operatorname{forward}\left(q\right), \operatorname{backward}\left(q\right)\right) = \operatorname{ringIdentity}\left(\operatorname{QF}\left(q\right)\right) \land \left(\operatorname{compose}\left(\operatorname{backward}\left(q\right), \operatorname{forward}\left(q\right)\right) = \operatorname{ringIdentity}\left(\operatorname{QP}\left(q\right)\right) \land \left(\left(\forall p \in IntPolynomial,\; \operatorname{ringEquiv}\left(q, \operatorname{pp}\left(q, \operatorname{inclusion}\left(p\right)\right)\right) = \operatorname{fp}\left(q, p\right)\right) \land \left(\left(\forall p \in IntPolynomial,\; \operatorname{inverse}\left(\operatorname{ringEquiv}\left(q\right), \operatorname{fp}\left(q, p\right)\right) = \operatorname{pp}\left(q, \operatorname{inclusion}\left(p\right)\right)\right) \land \left(\operatorname{ringEquiv}\left(q, \operatorname{pp}\left(q, X\right)\right) = \operatorname{fp}\left(q, X\right) \land \left(\operatorname{ringEquiv}\left(q, \operatorname{pp}\left(q, \operatorname{C}\left(resetLabel\right)\right)\right) = \operatorname{fp}\left(q, \operatorname{W}\left(q\right)\right) \land \left(\left(\forall z \in Int,\; \operatorname{ringEquiv}\left(q, \operatorname{pp}\left(q, \operatorname{C}\left(\operatorname{integerScalar}\left(z\right)\right)\right)\right) = \operatorname{fp}\left(q, \operatorname{C}\left(z\right)\right)\right) \land \left(\operatorname{ringEquiv}\left(q, 1\right) = 1 \land \left(q = 1 \Rightarrow \operatorname{ringEquiv}\left(q, \operatorname{pp}\left(q, \operatorname{C}\left(resetLabel\right)\right)\right) = \operatorname{fp}\left(q, X\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResetSignIntegerCyclic.literal_presentation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

compose is RingHom.comp and ringIdentity is RingHom.id. IntPolynomial means Polynomial Int. integerScalar is algebraMap Int R. inverse is the RingEquiv inverse. ringEquiv has forward as its actual forward map and backward as its actual inverse. Every natural q is included; the intended native consumer uses q>0. At q=1, S=1, F=X^2-1 and W-X=-F, so the literal sign class maps to the time class.

The geometric identity X^q-(X-1)*S=1 yields the exact certificates X^q-W*S=F and W^2-1=((X-1)^2-1)*F. Thus [W]^2=1 in QF. signHom sends 1 to 1 and oddTau to [W], with multiplication proved by the actual two Sign cases. coefficientHom is MonoidAlgebra.lift of this monoid hom, and forwardPolynomial is Polynomial.eval2RingHom with X sent to [X]. The first certificate kills P, so the map descends. flip_twice 1 gives resetLabel^2=1. In the source ring, inclusion(F)=(X^q+C(resetLabel)*inclusion(S))*P and C(resetLabel)-inclusion(W)=(X-1+C(resetLabel))*P. The first kills F for backward=pp composed with inclusion; the second identifies the source coefficient. Quotient and polynomial ring-hom extensionality, then MonoidAlgebra.ringHom_ext on scalars and both Sign elements, prove the two inverse identities.

The next consumer is the actual integer-linear map from QF to DimensionGroup(resetMatrix q), obtained through ringEquiv inverse, the accepted arbitrary-ring cyclicEquiv at R/resetLabel, and resetNativeEquiv inverse. It must prove that 1 is stage-zero e0 and X intertwines original resetTheta, then use LinearEquiv.ofAEval for the Int[X]-module chart. Native stage n uses inverse time powers. Transferring oddTau=W(Theta) additionally requires the concrete coefficient law for groupAction, resetNativeEquiv_stage and DirectLimit.map_apply_of; integer linearity alone is insufficient. This module proves no native chart, square range/image correspondence, four oriented branches, exact resetFiveClock, centralizer/units, or full original rho character/action. The result is a repository derivation using the standard group-algebra and polynomial universal properties, without a claim of literature novelty.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetSignIntegerCyclic.geometric`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetSignIntegerCyclic.literal_presentation`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetSignIntegerCyclic.sign_square`
- Dependency: [D5/S1/Recurrence/FiniteCompanionCyclicModule](../../../S1/Recurrence/FiniteCompanionCyclicModule.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/ResetNativeIntegralDefect](ResetNativeIntegralDefect.md)

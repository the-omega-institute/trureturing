# Finite Event Coupling Sharp Bounds

## Abstract

A two-event coupling polytope has an explicit primal witness, replayable dual-slack certificate, and exact sharp projection bounds.

The feasible object is a normalized nonnegative law on two Boolean event indicators with two prescribed marginals. Its target coordinate is the true-true intersection cell.

Normalization and the two marginal rows produce exact slack identities for the Fréchet lower plane and the two upper planes. An additional linear cap on disagreement contributes a fourth lower plane.

The explicit four-cell coupling realizes every target in the resulting closed interval. The necessity proof replays the certificate, while the sufficiency proof constructs the primal witness.

For a five-mode Fibonacci window law p on null, low 2, high 5, ends 25 and middle 3, all cell masses are real, nonnegative and sum to one. Set X=p(low)+p(ends), Y=p(high)+p(ends), Z=p(middle), r=1-Z and kappa=p(ends). The endpoint and middle occupancy coordinates satisfy X,Y,Z>=0, X+Z<=1 and Y+Z<=1. PathStableSetPolytope.convexHull_three_pyramid applies in coordinate order (X,Z,Y), identifying this domain with the convex hull of the five admissible three-bit words.

The full fixed-coordinate family has cells (r-X-Y+kappa, X-kappa, Y-kappa, kappa, Z). Nonnegativity is exactly max(0,X+Y-r)<=kappa<=min(X,Y), together with Z>=0. Every coarse point is feasible: the lower endpoint lies below both X and Y. When r>0, divide the four bottom cells by r and apply event_coupling_primal_bounds and event_coupling_target_feasible_iff with left marginal X/r, right marginal Y/r and intersection kappa/r. Rescaling gives the complete sharp interval, including its zero-cell endpoints. Its length is w=min(X,Y,r-X,r-Y); a zero length gives a singleton, and a positive length gives distinct laws with identical coarse coordinates.

The bottom determinant is Delta=p(null)p(ends)-p(low)p(high)=r*kappa-X*Y. For r>0 it recovers kappa=(X*Y+Delta)/r and hence all five cells. CrossWorldIndependenceSharpBounds.independent_joint_event_eq_product applies to the normalized bottom table. Delta=0 is equivalent to factorization of all four conditional cells into their Boolean marginal products. Conversely eventCoupling_isIndependent supplies the product completion kappa*=X*Y/r, which remains a legal five-mode law. This concerns independence given the middle is absent. It is not unconditional endpoint independence when Z is positive: at X=Y=2/5, Z=1/5, kappa=1/5, Delta=0 but kappa differs from X*Y. At r=0 nonnegativity forces the unique middle law, with X=Y=kappa=0; no division by r is used.

For any real target f on the same five letters, Jf=f(ends)-f(low)-f(high)+f(null). Its expectation is (r-X-Y)f(null)+X*f(low)+Y*f(high)+Z*f(middle)+Jf*kappa. Thus its difference from the product completion is Jf*Delta/r only for r>0. The target image of the full kappa interval is the unordered closed interval between its endpoint expectations, by Mathlib Set.image_const_mul_uIcc and Set.image_const_add_uIcc. Its width is abs(Jf)*w, with no sign restriction on Jf. At the apex the expectation is f(middle). The parameter f specifies the mathematical target; it defines no aggregate score or acquisition rule. The coupling bounds and affine interval-image identities establish these consequences by normalization.

**Theorem 1.1 (Marginal rows generate a replayable dual-slack certificate).**

$$\forall mass \in \operatorname{Prod}\left(Bool, Bool\right) \to Real, leftMarginal \in Real, rightMarginal \in Real, disagreementCap \in Real,\; \operatorname{IsEventCoupling}\left(mass, leftMarginal, rightMarginal\right) \Rightarrow \operatorname{EventCouplingDualCertificate}\left(mass, leftMarginal, rightMarginal, disagreementCap\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Causal/FiniteEventCouplingSharpBounds.event_coupling_dual_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every feasible coupling and every proposed disagreement cap, the four exact slack identities hold. Nonnegativity and the cap can then be checked separately when the certificate is replayed.

**Theorem 1.2 (The disagreement-constrained interval is exactly sharp).**

$$\forall leftMarginal \in Real, rightMarginal \in Real, disagreementCap \in Real, target \in Real,\; \left(\operatorname{max}\left(\operatorname{max}\left(0, leftMarginal + rightMarginal - 1\right), \frac{leftMarginal + rightMarginal - disagreementCap}{2}\right) \le target \land target \le \operatorname{min}\left(leftMarginal, rightMarginal\right)\right) \Leftrightarrow \left(\exists mass \in \operatorname{Prod}\left(Bool, Bool\right) \to Real,\; \operatorname{IsEventCoupling}\left(mass, leftMarginal, rightMarginal\right) \land \left(\operatorname{disagreementMass}\left(mass\right) \le disagreementCap \land mass\left(\operatorname{pair}\left(true, true\right)\right) = target\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Causal/FiniteEventCouplingSharpBounds.event_coupling_target_feasible_with_disagreement_cap_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A real target lies in the displayed interval exactly when some normalized nonnegative coupling has the required marginals, obeys the disagreement cap, and realizes that target.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Causal/FiniteEventCouplingSharpBounds.event_coupling_dual_certificate`
- Truth anchor: `D5/S3/ConceptDynamics/Causal/FiniteEventCouplingSharpBounds.event_coupling_target_feasible_with_disagreement_cap_iff`
- Dependency: [D5/S3/ConceptDynamics/Causal/BenefitProbabilityBounds](BenefitProbabilityBounds.md)

# Empirical Identifiability

## Abstract

Protocol outcomes determine exactly which model properties descend uniquely.

**Theorem 1.1 (Empirical quotient descent and residual obstruction).**

$$\forall P, Theta, Y,\ Out: P \to Theta \to \operatorname{Type}, T: Theta \to Y,\ ((\exists! d: Theta_{emp} \to Y, T(theta) = d(class(theta))) \iff (\forall theta, thetaPrime,\ (\forall P, Out(P)(theta) = Out(P)(thetaPrime)) \Rightarrow T(theta) = T(thetaPrime))) \land ((\exists theta, thetaPrime,\ (\forall P, Out(P)(theta) = Out(P)(thetaPrime)) \land T(theta) \neq T(thetaPrime)) \Rightarrow \neg\exists d: Theta_{emp} \to Y, T(theta) = d \circ class).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/EmpiricalIdentifiability.empirical_identifiability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The empirical setoid is constructed from equality of every allowed protocol outcome, and the quotient and class map are the canonical ones for that source relation.

A property descends to exactly one quotient map precisely when it is constant on every empirical-equivalence fiber. An empirically equivalent pair with different property values rules out every possible quotient factor.

Pinned quotient constructors were applied directly; no source object is defined as the target conclusion.

## Can three coupling readings identify a matching scale?

Consider three inverse gauge couplings at a fixed reference scale in a one-loop matching model. Write E for the change in their three readings multiplied by 2 pi. Let a be 2 pi times the change of the inverse unified coupling, and t the change in the log matching scale. With matching scale mu and heavy masses M_D and M_C, let k and c be the changes in log(M_D^2/mu^2) and log(M_C^2/mu^2). Allow the two positive ratios to vary independently. In a fixed threshold regime, assume E = a(1,1,1) + t b - k D/2 - c C/2 with b = (41/10,-19/6,-7), D = (2/15,2/3,1/3) and C = (2/15,0,1/3).

Equality of all three readings means E = 0. Ten times the first component minus ten times the third gives 111t + k + c = 0. Six times the second minus six times the third gives 23t - k + c = 0. Adding these equations fixes t = -c/67. The second difference then fixes k = 44c/67, and setting the second reading to zero gives a = 23c/134. Substitution in all three components gives zero for every real c. Thus the entire fiber through a given parameter point is its translate by c(23/134,-1/67,44/67,1), intersected with the parameter domain.

Take the protocol outcome to be the triple of readings and the property to be the log matching scale. At an interior parameter point, a sufficiently small nonzero c preserves the threshold regime and moves the log scale. These two points have the same outcome and different property values, so the scale cannot descend to their empirical quotient. An independent determination of either mass coefficient which varies along this line fixes the position on the fiber. The charge vectors and the one-loop matching law are inputs to this calculation.

## References

- Truth anchor: `D5/S3/ConceptDynamics/EmpiricalIdentifiability.empirical_identifiability`

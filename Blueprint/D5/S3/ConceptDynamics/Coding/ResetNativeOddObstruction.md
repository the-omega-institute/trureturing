# The surviving native integer odd class

## Abstract

The surviving native integer odd class.

Display conventions. Type ranges over the source universes; class-instance binders show the stated finite, decidable, algebraic and topological hypotheses. Essential G requires an actual incoming and outgoing edge at every vertex. History G is the subtype of all Int-indexed edge sequences satisfying target(x k)=source(x (k+1)); coordinate is subtype evaluation. Homeomorph, Equiv and MonoidHom display Lean homeomorphism, equivalence and multiplicative-hom types. IntModule is Module Int; IntEnd is Module.End Int; IntLinearMap and IntLinearEquiv are the corresponding Int-linear types. recordType and typeAlias label a structure or abbreviation, and hasType labels a definition's result type. image is whole Set.image; compose is LinearMap.comp; linearIdentity is LinearMap.id; endSum is linear-map addition. power is the source's natural power, rightMultiply is Matrix.vecMul, and intCast is the Nat-to-Int coercion. Other display aliases are expanded in the corresponding definitions; proof arguments are determined by the displayed telescope, not new hypotheses.

**Definition 1.1 (An explicit row with both integer sign coefficients).**

$$\forall q \in Nat, j \in \operatorname{Fin}\left(q\right),\; \operatorname{resetOddVector}\left(q\right)\left(j\right) = \operatorname{integerScale}\left(\operatorname{power}\left(-1, \operatorname{finValue}\left(j\right)\right), \operatorname{antiUnit}\left(\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/ResetNativeOddObstruction.resetOddVector` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

resetOddVector q belongs to VertexModule Sign q, with Sign=Multiplicative Bool and tau=ofAdd true. antiUnit means single (1:Sign) (1:Int) - single tau (1:Int) in MonoidAlgebra Int Sign. integerScale is the Int module action and finValue(j)=j.val. Thus w_i=(-1)^i(1-tau) retains both coefficients. No positivity or odd premise is needed to define the row.

**Definition 1.2 (Theta is induced by the original row transition).**

$$\forall q \in Nat,\; \operatorname{hasType}\left(\operatorname{resetTheta}\left(q\right), \operatorname{IntEnd}\left(\operatorname{DimensionGroup}\left(\operatorname{resetMatrix}\left(q\right)\right)\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/ResetNativeOddObstruction.resetTheta` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

resetTheta q=induced (transition(resetMatrix q)) (transition(resetMatrix q)) (Commute.refl _), on the existing DimensionGroup(resetMatrix q). hasType displays the definition's type. The integerMatrix casts the original natural group matrix into Int[C2], and transition is the original row toLinearMapRight'. The reset label multiplies each input coordinate on the RIGHT. groupAction(resetMatrix q) tau is the separate complement action; it is not the definition of Theta.

**Theorem 1.3 (A nonzero coefficient survives every transition iterate).**

$$\forall q \in Nat, hq \in \operatorname{NatPositive}\left(q\right), ho \in \operatorname{Odd}\left(q\right), k \in Nat,\; \operatorname{identityCoefficientAtZero}\left(\operatorname{power}\left(\operatorname{transition}\left(\operatorname{resetMatrix}\left(q\right)\right), k\right)\left(\operatorname{resetOddVector}\left(q\right)\right), hq\right) = \operatorname{power}\left(-1, k\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResetNativeOddObstruction.reset_odd_transition_pow_coeff_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

identityCoefficientAtZero(v,hq) is (v (0 : Fin q)).coeff (1:Sign), using hq to construct the zero suffix. reset_odd_transition computes T w=-w: the odd alternating sum equals one, multiplication of 1-tau by tau gives its negative, and every successor coordinate reads its predecessor. reset_odd_transition_pow then gives T^k w=(-1)^k w for every natural k. Its displayed suffix-zero identity coefficient is the nonzero integer unit (-1)^k. The pairwise alternating-sum induction begins at q=1; no mixing or q>=3 hypothesis is used.

**Theorem 1.4 (A genuinely surviving original integer class is killed by id plus Theta).**

$$\forall q \in Nat, hq \in \operatorname{NatPositive}\left(q\right), ho \in \operatorname{Odd}\left(q\right),\; \operatorname{resetOddClass}\left(q\right) \ne 0 \land \operatorname{endSum}\left(\operatorname{linearIdentity}\left(\operatorname{DimensionGroup}\left(\operatorname{resetMatrix}\left(q\right)\right)\right), \operatorname{resetTheta}\left(q\right)\right)\left(\operatorname{resetOddClass}\left(q\right)\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResetNativeOddObstruction.reset_odd_killed_class` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

resetOddClass q is the ORIGINAL natural-stage colimit class at stage zero of resetOddVector q. If it were zero, Module.DirectLimit.exists_eq_of_of_eq would force a later iterate of that row to vanish, contradicting its explicit coefficient (-1)^k. The identity plus resetTheta kills the class because T w=-w. This survival argument uses neither transition injectivity nor a torsion-free premise, nor a spectral-radius or Parry scalar argument. It includes the deterministic odd case q=1.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetNativeOddObstruction.resetOddVector`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetNativeOddObstruction.resetTheta`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetNativeOddObstruction.reset_odd_killed_class`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetNativeOddObstruction.reset_odd_transition_pow_coeff_one`
- Dependency: [D5/S3/ConceptDynamics/Coding/InertGroupBlockConjugacy](InertGroupBlockConjugacy.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/ResetNumberedHistories](ResetNumberedHistories.md)

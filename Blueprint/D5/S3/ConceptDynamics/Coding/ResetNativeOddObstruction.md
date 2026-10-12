# The surviving native integer odd class

## Abstract

The surviving native integer odd class.

Display conventions. Type ranges over the source universes; class-instance binders show the stated finite, decidable, algebraic and topological hypotheses. Essential G requires an actual incoming and outgoing edge at every vertex. History G is the subtype of all Int-indexed edge sequences satisfying target(x k)=source(x (k+1)); coordinate is subtype evaluation. Homeomorph, Equiv and MonoidHom display Lean homeomorphism, equivalence and multiplicative-hom types. IntModule is Module Int; IntEnd is Module.End Int; IntLinearMap and IntLinearEquiv are the corresponding Int-linear types. recordType and typeAlias label a structure or abbreviation, and hasType labels a definition's result type. image is whole Set.image; compose is LinearMap.comp; linearIdentity is LinearMap.id; endSum is linear-map addition. power is the source's natural power, rightMultiply is Matrix.vecMul, and intCast is the Nat-to-Int coercion. Other display aliases are expanded in the corresponding definitions; proof arguments are determined by the displayed telescope, not new hypotheses.

**Definition 1.1 (The nonidentity reset sign).**

$$oddTau = \operatorname{ofAdd}\left(true\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/ResetNativeOddObstruction.oddTau` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Sign is Multiplicative Bool; oddTau is ofAdd true, the nonidentity sign. This is the label used by the original coordinate formulas.

**Definition 1.2 (The integral reset label).**

$$resetLabel = \operatorname{single}\left(oddTau, 1\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/ResetNativeOddObstruction.resetLabel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

single is MonoidAlgebra.single in MonoidAlgebra Int Sign. resetLabel is the original right-multiplication label, with coefficient one at oddTau.

**Theorem 1.3 (The original transition at coordinate zero).**

$$\forall N \in Nat, v \in \operatorname{VertexModule}\left(Sign, \operatorname{succ}\left(N\right)\right),\; \operatorname{transition}\left(\operatorname{resetMatrix}\left(\operatorname{succ}\left(N\right)\right)\right)\left(v, 0\right) = \operatorname{mul}\left(\operatorname{sumCoordinates}\left(v\right), resetLabel\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResetNativeOddObstruction.transition_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

succ(N)=N+1; sumCoordinates(v) is the sum over Fin(N+1), and zero is the zero Fin coordinate. The formula is T(v)(0)=(sum v)*resetLabel in the original integer right-row convention. It is the coordinate fact used by both the odd obstruction and the finite companion bridge.

**Theorem 1.4 (The original transition at successor coordinates).**

$$\forall N \in Nat, v \in \operatorname{VertexModule}\left(Sign, \operatorname{succ}\left(N\right)\right), j \in \operatorname{Fin}\left(N\right),\; \operatorname{transition}\left(\operatorname{resetMatrix}\left(\operatorname{succ}\left(N\right)\right)\right)\left(v, \operatorname{finSucc}\left(j\right)\right) = v\left(\operatorname{castSucc}\left(j\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResetNativeOddObstruction.transition_succ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For j:Fin N, finSucc(j) is j.succ and castSucc(j) is j.castSucc in Fin(N+1). Thus T(v)(j.succ)=v(j.castSucc), including the empty successor family at N=0. Both consumers directly apply this original coordinate fact.

**Definition 1.5 (An explicit row with both integer sign coefficients).**

$$\forall q \in Nat, j \in \operatorname{Fin}\left(q\right),\; \operatorname{resetOddVector}\left(q\right)\left(j\right) = \operatorname{integerScale}\left(\operatorname{power}\left(-1, \operatorname{finValue}\left(j\right)\right), \operatorname{antiUnit}\left(\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/ResetNativeOddObstruction.resetOddVector` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

resetOddVector q belongs to VertexModule Sign q, with Sign=Multiplicative Bool and tau=ofAdd true. antiUnit means single (1:Sign) (1:Int) - single tau (1:Int) in MonoidAlgebra Int Sign. integerScale is the Int module action and finValue(j)=j.val. Thus w_i=(-1)^i(1-tau) retains both coefficients. No positivity or odd premise is needed to define the row.

**Theorem 1.6 (The original alternating identity coefficient).**

$$\forall q \in Nat, i \in \operatorname{Fin}\left(q\right),\; \operatorname{coeff}\left(\operatorname{resetOddVector}\left(q\right)\left(i\right), 1\right) = \operatorname{power}\left(-1, \operatorname{finValue}\left(i\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResetNativeOddObstruction.resetOddVector_coeff_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The identity coefficient of the original row w_i is (-1)^i. It gives both the surviving iterate coefficient and the native character pairing.

**Definition 1.7 (Theta is induced by the original row transition).**

$$\forall q \in Nat,\; \operatorname{hasType}\left(\operatorname{resetTheta}\left(q\right), \operatorname{IntEnd}\left(\operatorname{DimensionGroup}\left(\operatorname{resetMatrix}\left(q\right)\right)\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/ResetNativeOddObstruction.resetTheta` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

resetTheta q=induced (transition(resetMatrix q)) (transition(resetMatrix q)) (Commute.refl _), on the existing DimensionGroup(resetMatrix q). hasType displays the definition's type. The integerMatrix casts the original natural group matrix into Int[C2], and transition is the original row toLinearMapRight'. The reset label multiplies each input coordinate on the RIGHT. groupAction(resetMatrix q) tau is the separate complement action; it is not the definition of Theta.

**Theorem 1.8 (Theta acts on each original stage by its row transition).**

$$\forall q \in Nat, n \in Nat, v \in \operatorname{VertexModule}\left(Sign, q\right),\; \operatorname{resetTheta}\left(q\right)\left(\operatorname{nativeStage}\left(q, n, v\right)\right) = \operatorname{nativeStage}\left(q, n, \operatorname{transition}\left(\operatorname{resetMatrix}\left(q\right)\right)\left(v\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResetNativeOddObstruction.resetTheta_apply_of` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

nativeStage(q,n,v) is Module.DirectLimit.of Int Nat (fun _ => VertexModule Sign q) (stationaryTransition (transition (resetMatrix q))) n v. The identity follows from Module.DirectLimit.map_apply_of for the stationary transition. It holds for every natural q and n, without positivity or parity assumptions. The native stage-zero identification uses this identity in resetNativeEquiv_theta to intertwine Theta with the original right-row transition.

**Theorem 1.9 (A nonzero coefficient survives every transition iterate).**

$$\forall q \in Nat, hq \in \operatorname{NatPositive}\left(q\right), ho \in \operatorname{Odd}\left(q\right), k \in Nat,\; \operatorname{identityCoefficientAtZero}\left(\operatorname{power}\left(\operatorname{transition}\left(\operatorname{resetMatrix}\left(q\right)\right), k\right)\left(\operatorname{resetOddVector}\left(q\right)\right), hq\right) = \operatorname{power}\left(-1, k\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResetNativeOddObstruction.reset_odd_transition_pow_coeff_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

identityCoefficientAtZero(v,hq) is (v (0 : Fin q)).coeff (1:Sign), using hq to construct the zero suffix. reset_odd_transition computes T w=-w: the odd alternating sum equals one, multiplication of 1-tau by tau gives its negative, and every successor coordinate reads its predecessor. reset_odd_transition_pow then gives T^k w=(-1)^k w for every natural k. Its displayed suffix-zero identity coefficient is the nonzero integer unit (-1)^k. The pairwise alternating-sum induction begins at q=1; no mixing or q>=3 hypothesis is used.

**Theorem 1.10 (A genuinely surviving original integer class is killed by id plus Theta).**

$$\forall q \in Nat, hq \in \operatorname{NatPositive}\left(q\right), ho \in \operatorname{Odd}\left(q\right),\; \operatorname{resetOddClass}\left(q\right) \ne 0 \land \operatorname{endSum}\left(\operatorname{linearIdentity}\left(\operatorname{DimensionGroup}\left(\operatorname{resetMatrix}\left(q\right)\right)\right), \operatorname{resetTheta}\left(q\right)\right)\left(\operatorname{resetOddClass}\left(q\right)\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResetNativeOddObstruction.reset_odd_killed_class` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

resetOddClass q is the ORIGINAL natural-stage colimit class at stage zero of resetOddVector q. If it were zero, Module.DirectLimit.exists_eq_of_of_eq would force a later iterate of that row to vanish, contradicting its explicit coefficient (-1)^k. The identity plus resetTheta kills the class because T w=-w. This survival argument uses neither transition injectivity nor a torsion-free premise, nor a spectral-radius or Parry scalar argument. It includes the deterministic odd case q=1.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetNativeOddObstruction.oddTau`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetNativeOddObstruction.resetLabel`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetNativeOddObstruction.resetOddVector`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetNativeOddObstruction.resetOddVector_coeff_one`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetNativeOddObstruction.resetTheta`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetNativeOddObstruction.resetTheta_apply_of`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetNativeOddObstruction.reset_odd_killed_class`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetNativeOddObstruction.reset_odd_transition_pow_coeff_one`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetNativeOddObstruction.transition_succ`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetNativeOddObstruction.transition_zero`
- Dependency: [D5/S3/ConceptDynamics/Coding/InertGroupBlockConjugacy](InertGroupBlockConjugacy.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/ResetNumberedHistories](ResetNumberedHistories.md)

# Coupled integral reset units

## Abstract

Integral compatibility yields every reset unit with unique signed time and two independent signs.

Throughout this module q is exactly 2. QF(2) is the original quotient Int[X]/(X^4-X^2-2X-1), Plus(2)=Int[X]/(X^2-X-1), and Minus(2)=Int[X]/(X^2+X+1). ResetIntegralGluing supplies the faithful compatible-pair reconstruction over the literal common coefficient-mod-two quotient. All units and every signed integer time exponent are retained.

**Theorem 1.1 (Literal quadratic charts and the four-element field).**

$$\operatorname{IsField}\left(\operatorname{Common}\left(2\right)\right) \land \left(\operatorname{card}\left(\operatorname{Common}\left(2\right)\right) = 4 \land \left(\operatorname{golden}\left(\operatorname{root}\left(\operatorname{f}\left(2\right)\right)\right) = phi \land \left(\operatorname{eisenstein}\left(\operatorname{root}\left(\operatorname{g}\left(2\right)\right)\right) = omega \land \left(\operatorname{common}\left(\operatorname{root}\left(\operatorname{reduce}\left(\operatorname{g}\left(2\right)\right)\right)\right) = omega \land \left(\left(\forall z \in \operatorname{Plus}\left(2\right),\; \operatorname{common}\left(\operatorname{rplus}\left(2, z\right)\right) = \operatorname{goldenReduce}\left(\operatorname{golden}\left(z\right)\right)\right) \land \left(\forall z \in \operatorname{Minus}\left(2\right),\; \operatorname{common}\left(\operatorname{rminus}\left(2, z\right)\right) = \operatorname{modTwo}\left(\operatorname{eisenstein}\left(z\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResetIntegralUnits.quadratic_charts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

golden is the existing goldenAdjoinRootEquiv after equality of defining polynomials; it fixes X to phi. eisenstein and common specialize the original CalderonReciprocalMoments.coordinateEquiv at T=-1,N=1 over Int and ZMod 2. Ideal.quotEquivOfEq transports the defining polynomial to X^2-C(-1)*X+C(1); the supplier sends the root to omega=(0,1), and its inverse sends (a,b) to [a+bX]. The supplier's rootToCoordinates is used directly for generator simplification. Its generic telescope requires only a commutative coefficient ring, with no prime or p-adic hypothesis. Each omega in the displayed formula has the coefficient ring prescribed by its chart. Both reductions are literally (a,b) to (a mod 2,b mod 2). The existing inert_eisenstein_quotient_frobenius at ell=2 supplies maximality, the quotient field and cardinal four, transported through these actual equivalences. The reduction clauses are consumed in component_compatibility. This is a helper.

**Definition 1.2 (Forward time with a literal integral inverse).**

$$\operatorname{hasType}\left(xUnit, \operatorname{Units}\left(\operatorname{QF}\left(2\right)\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/ResetIntegralUnits.xUnit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

xUnit has value [X] and inverse [X^3-X-2]; multiplication gives one by the exact F relation. wUnit has value [W], W=1+X+X^2-X^3, and inverse itself by the original sign_square certificate. The component images of x,w,-1 are (phi,omega), (1,-1), and (-1,-1), respectively. Negative time powers use this integral inverse.

**Theorem 1.3 (Every unit has a unique full normal form).**

$$\forall u \in \operatorname{Units}\left(\operatorname{QF}\left(2\right)\right),\; \exists p \in \operatorname{product}\left(Int, \operatorname{product}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right)\right)\right),\; u = \operatorname{normal}\left(\operatorname{fst}\left(p\right), \operatorname{fst}\left(\operatorname{snd}\left(p\right)\right), \operatorname{snd}\left(\operatorname{snd}\left(p\right)\right)\right) \land \left(\forall r \in \operatorname{product}\left(Int, \operatorname{product}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right)\right)\right),\; u = \operatorname{normal}\left(\operatorname{fst}\left(r\right), \operatorname{fst}\left(\operatorname{snd}\left(r\right)\right), \operatorname{snd}\left(\operatorname{snd}\left(r\right)\right)\right) \Rightarrow r = p\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResetIntegralUnits.unit_normal_form` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

normal(n,a,b)=(-1)^a.val*wUnit^b.val*xUnit^n, with n:Int and a,b:Fin 2. Use the existing golden_units_eq_signed_phi_pow for the plus component. Divide by its scalar sign and signed time power. The normalized plus component is one, so compatibility forces the minus component to reduce to one. At its original EisensteinCohnReductionCore owner, unit_modTwo gives imaginary coefficient zero; norm_unit_one then forces the real coefficient to be 1 or -1. Faithful integral gluing reconstructs the normalized unit as 1 or wUnit. signedPhiPower_unique fixes a,n, and the integral Eisenstein component distinguishes b=0 from b=1. No six-unit classification is reproved; the two signs are independent.

**Definition 1.4 (Oriented unit group equivalence).**

$$\operatorname{hasType}\left(unitsEquiv, \operatorname{GroupEquiv}\left(\operatorname{Units}\left(\operatorname{QF}\left(2\right)\right), \operatorname{product}\left(\operatorname{Multiplicative}\left(Int\right), \operatorname{product}\left(\operatorname{Multiplicative}\left(\operatorname{ZMod}\left(2\right)\right), \operatorname{Multiplicative}\left(\operatorname{ZMod}\left(2\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/ResetIntegralUnits.unitsEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

parameterHom sends (n,a,b) to normal(n,a,b); unitsEquiv is the inverse of that bijective group homomorphism. Parameter order is signed time, scalar sign, then original Sign involution. The group law uses integer exponent addition and the two square-one identities. Thus the inverse equivalence sends time 1 to xUnit, the first sign to scalar -1, and the second sign to wUnit.

The new bridge is faithful integral reconstruction and its use to recover an arbitrary unit from the reduction kernel. Component unit classifications and chart transport are reused helpers. This is a repository synthesis with standard quotient and quadratic-algebra APIs; no literature novelty is claimed. ResetNativeUnitNormalForm consumes it on the original dimension group. The exact original rho image and exclusion of scalar minus sign remain open.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetIntegralUnits.quadratic_charts`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetIntegralUnits.unit_normal_form`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetIntegralUnits.unitsEquiv`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetIntegralUnits.xUnit`
- Dependency: [D5/S0/Carrier/AlgebraicModel](../../../S0/Carrier/AlgebraicModel.md)
- Dependency: [D5/S3/Arith/Congruence/QuadraticOrderMoments/CalderonReciprocalMoments](../../Arith/Congruence/QuadraticOrderMoments/CalderonReciprocalMoments.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/ResetIntegralGluing](ResetIntegralGluing.md)
- Dependency: [D5/S3/Factorization/QuadraticIdeals/EisensteinCohnReductionCore](../../Factorization/QuadraticIdeals/EisensteinCohnReductionCore.md)
- Dependency: [D5/S3/Factorization/QuadraticIdeals/InertEisensteinFrobenius](../../Factorization/QuadraticIdeals/InertEisensteinFrobenius.md)

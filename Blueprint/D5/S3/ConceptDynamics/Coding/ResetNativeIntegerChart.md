# Original native square-time arithmetic

## Abstract

The original native square-time quotient has four oriented integral arithmetic ring charts, a canonical projection, and bounded generation of every target unit by actual forward shifts.

For every q>0, including q=1, R is literally MonoidAlgebra Int Sign, Sign is Multiplicative Bool, resetLabel is single (ofAdd true) 1, and QF(q) is Int[X]/(F(q)) from ResetSignIntegerCyclic. Native(q) is the ORIGINAL DimensionGroup(resetMatrix q), with the canonical AddCommGroup.toIntModule instance used by the full rho owner. nativeStage is the original DirectLimit.of. Theta is original forward resetTheta; U is actual groupAction(resetMatrix q)(ofAdd true). These operators are distinguished until concrete coefficient naturality is proved.

**Definition 1.1 (An actual integral equivalence).**

$$\forall q \in Nat, hq \in \operatorname{NatPositive}\left(q\right),\; \operatorname{hasType}\left(\operatorname{nativeIntEquiv}\left(q, hq\right), \operatorname{IntLinearEquiv}\left(\operatorname{QF}\left(q\right), \operatorname{Native}\left(q\right)\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/ResetNativeIntegerChart.nativeIntEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The map is the composite of ringEquiv.symm, the existing FiniteCompanionCyclicModule.cyclicEquiv at R/resetLabel, removal of its AEval wrapper, and resetNativeEquiv.symm. Additive equivalences are made integer-linear by toAddEquiv.toIntLinearEquiv. The inverse native map is actual stage zero; no rank or cardinality argument is used.

**Definition 1.2 (The genuine polynomial module chart).**

$$\forall q \in Nat, hq \in \operatorname{NatPositive}\left(q\right),\; \operatorname{hasType}\left(\operatorname{nativePolynomialEquiv}\left(q, hq\right), \operatorname{PolynomialLinearEquiv}\left(\operatorname{QF}\left(q\right), \operatorname{AEval}\left(\operatorname{resetTheta}\left(q\right)\right)\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/ResetNativeIntegerChart.nativePolynomialEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Only after Phi([X]b)=Theta(Phi(b)) is proved does LinearEquiv.ofAEval promote Phi inverse from the native group to QF. Its inverse is QF equivalent over Int[X] to Module.AEval'(Theta). AEvalOf is the canonical integer-linear identification with that type synonym.

**Theorem 1.3 (Normalized time, stage and coefficient laws).**

$$\forall q \in Nat, hq \in \operatorname{NatPositive}\left(q\right),\; \operatorname{nativeIntEquiv}\left(q, hq, 1\right) = \operatorname{nativeStage}\left(q, 0, \operatorname{e0}\left(q, hq\right)\right) \land \left(\left(\forall b \in \operatorname{QF}\left(q\right),\; \operatorname{nativeIntEquiv}\left(q, hq, \operatorname{multiply}\left(\operatorname{fp}\left(q, X\right), b\right)\right) = \operatorname{apply}\left(\operatorname{resetTheta}\left(q\right), \operatorname{nativeIntEquiv}\left(q, hq, b\right)\right)\right) \land \left(\left(\forall p \in IntPolynomial, b \in \operatorname{QF}\left(q\right),\; \operatorname{nativeIntEquiv}\left(q, hq, \operatorname{multiply}\left(\operatorname{fp}\left(q, p\right), b\right)\right) = \operatorname{apply}\left(\operatorname{aeval}\left(\operatorname{resetTheta}\left(q\right), p\right), \operatorname{nativeIntEquiv}\left(q, hq, b\right)\right)\right) \land \left(\left(\forall z \in Int, b \in \operatorname{QF}\left(q\right),\; \operatorname{nativeIntEquiv}\left(q, hq, \operatorname{integerScale}\left(z, b\right)\right) = \operatorname{integerScale}\left(z, \operatorname{nativeIntEquiv}\left(q, hq, b\right)\right)\right) \land \left(\left(\forall b \in \operatorname{QF}\left(q\right),\; \operatorname{nativePolynomialEquiv}\left(q, hq, b\right) = \operatorname{AEvalOf}\left(\operatorname{resetTheta}\left(q\right), \operatorname{nativeIntEquiv}\left(q, hq, b\right)\right)\right) \land \left(\left(\forall n \in Nat, v \in \operatorname{VertexModule}\left(Sign, q\right),\; \operatorname{apply}\left(\operatorname{inverse}\left(\operatorname{nativeIntEquiv}\left(q, hq\right)\right), \operatorname{nativeStage}\left(q, n, v\right)\right) = \operatorname{ringEquiv}\left(q, \operatorname{pp}\left(q, \operatorname{coordinatePolynomial}\left(resetLabel, q, \operatorname{apply}\left(\operatorname{power}\left(\operatorname{resetInverse}\left(q, hq\right), n\right), v\right)\right)\right)\right)\right) \land \left(\left(\forall x \in \operatorname{Native}\left(q\right),\; \operatorname{apply}\left(\operatorname{resetNativeEquiv}\left(q, hq\right), \operatorname{apply}\left(\operatorname{groupAction}\left(\operatorname{resetMatrix}\left(q\right), \operatorname{ofAdd}\left(true\right)\right), x\right)\right) = \operatorname{apply}\left(\operatorname{leftTranslation}\left(\operatorname{ofAdd}\left(true\right)\right), \operatorname{apply}\left(\operatorname{resetNativeEquiv}\left(q, hq\right), x\right)\right)\right) \land \operatorname{groupAction}\left(\operatorname{resetMatrix}\left(q\right), \operatorname{ofAdd}\left(true\right)\right) = \operatorname{aeval}\left(\operatorname{resetTheta}\left(q\right), \operatorname{W}\left(q\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResetNativeIntegerChart.native_presentation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

NatPositive(q) means 0<q; IntPolynomial is Polynomial Int. multiply is quotient-ring multiplication, integerScale is integer module action, inverse is the linear-equivalence inverse, and power is composition power of an endomorphism. The theorem supplies normalization at original stage-zero e0, forward X intertwining, all exact polynomial and integer scalar laws, the underlying map of the polynomial chart, the explicit inverse coordinate polynomial at every stage, concrete native Sign naturality and U=aeval(Theta)(W).

At q=n+1, the original ResetSquareIntegralDefect.time_eq supplies the finite time bridge. Thus the existing coefficient-ring time is the original RIGHT-row forward transition, also when n=0. The ring bridge's X image and cyclicEquiv polynomial-linearity give the finite X law; resetNativeEquiv_theta gives the original native law. The promoted equivalence then supplies every polynomial action exactly. cyclic_presentation supplies the inverse coordinatePolynomial. resetNativeEquiv_stage supplies resetInverse raised to n: later stages use inverse time while X still denotes forward time.

For concrete coefficient naturality, exhaust an arbitrary native x using resetNativeEquiv.symm_apply_apply. Its actual inverse is stage-zero DirectLimit.of. groupAction unfolds to DirectLimit.map, whose map_apply_of sends that representative to the stage-zero leftTranslation of its row. resetNativeEquiv_stage at zero closes the equality, without re-proving inverse-power commutation. In the literal commutative Sign algebra, left translation by ofAdd true equals RIGHT multiplication by resetLabel. cyclicEquiv's C(resetLabel) action and ringEquiv's C(resetLabel) image [W] therefore transfer to the actual native U. Surjectivity of Phi and its polynomial law yield the endomorphism identity U=aeval(Theta)(W). Only integer linearity of resetNativeEquiv is used.

**Definition 1.4 (Both inverse oriented ring maps).**

$$\forall q \in Nat,\; \operatorname{hasType}\left(\operatorname{arithmeticChart}\left(q\right), \operatorname{RingEquiv}\left(\operatorname{SquareRing}\left(q\right), \operatorname{Target}\left(\operatorname{mod}\left(q, 4\right)\right)\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/ResetNativeIntegerChart.arithmeticChart` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The chart selects the actual zero, binary, five or Gaussian RingEquiv according to q mod 4. Each has actual forward and reverse maps, left and right inverse laws, multiplicativity and one. Its polynomial law fixes the forward-time orientation.

**Definition 1.5 (Canonical native arithmetic projection).**

$$\forall q \in Nat, hq \in \operatorname{NatPositive}\left(q\right),\; \operatorname{hasType}\left(\operatorname{eta}\left(q, hq\right), \operatorname{IntLinearMap}\left(\operatorname{Native}\left(q\right), \operatorname{Target}\left(\operatorname{mod}\left(q, 4\right)\right)\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/ResetNativeIntegerChart.eta` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Eta is the actual native chart inverse followed by bProjection and arithmeticChart. Its kernel is the original nativeSquare range; eta(generator)=1 fixes scalar normalization.

**Definition 1.6 (Ring structure transported through the proved additive quotient).**

$$\forall q \in Nat, hq \in \operatorname{NatPositive}\left(q\right),\; \operatorname{hasType}\left(\operatorname{nativeArithmeticEquiv}\left(q, hq\right), \operatorname{RingEquivWithTransportedStructure}\left(\operatorname{NativeSquare}\left(q\right), \operatorname{Target}\left(\operatorname{mod}\left(q, 4\right)\right), \operatorname{nativeSquareRing}\left(q, hq\right)\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/ResetNativeIntegerChart.nativeArithmeticEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

NativeSquare remains the original quotient by range(id+Theta^2). The named nativeSquareRing transports its ring structure through nativeSquareEquiv. The canonical mkQ formula and original addition law are part of native_square_arithmetic.

**Theorem 1.7 (The canonical native quotient and its arithmetic).**

$$\forall q \in Nat, hq \in \operatorname{NatPositive}\left(q\right),\; \left(\forall b \in \operatorname{QF}\left(q\right),\; \operatorname{nativeSquare}\left(q, \operatorname{nativeIntEquiv}\left(q, hq, b\right)\right) = \operatorname{nativeIntEquiv}\left(q, hq, \operatorname{multiply}\left(\operatorname{fp}\left(q, H\right), b\right)\right)\right) \land \left(\left(\forall x \in \operatorname{Native}\left(q\right),\; \operatorname{eta}\left(q, hq, x\right) = 0 \Leftrightarrow \left(\exists y \in \operatorname{Native}\left(q\right),\; \operatorname{nativeSquare}\left(q, y\right) = x\right)\right) \land \left(\operatorname{Surjective}\left(\operatorname{eta}\left(q, hq\right)\right) \land \left(\left(\forall x \in \operatorname{Native}\left(q\right),\; \operatorname{nativeArithmeticEquiv}\left(q, hq, \operatorname{mkQ}\left(\operatorname{range}\left(\operatorname{nativeSquare}\left(q\right)\right), x\right)\right) = \operatorname{eta}\left(q, hq, x\right)\right) \land \left(\left(\forall x \in \operatorname{NativeSquare}\left(q\right), y \in \operatorname{NativeSquare}\left(q\right),\; \operatorname{nativeArithmeticEquiv}\left(q, hq, \operatorname{add}\left(x, y\right)\right) = \operatorname{add}\left(\operatorname{nativeArithmeticEquiv}\left(q, hq, x\right), \operatorname{nativeArithmeticEquiv}\left(q, hq, y\right)\right)\right) \land \left(\operatorname{eta}\left(q, hq, \operatorname{generator}\left(q, hq\right)\right) = 1 \land \left(\left(\forall p \in IntPolynomial, x \in \operatorname{Native}\left(q\right),\; \operatorname{eta}\left(q, hq, \operatorname{apply}\left(\operatorname{aeval}\left(\operatorname{resetTheta}\left(q\right), p\right), x\right)\right) = \operatorname{multiply}\left(\operatorname{integerPolynomialEval}\left(p, \operatorname{targetTime}\left(\operatorname{mod}\left(q, 4\right)\right)\right), \operatorname{eta}\left(q, hq, x\right)\right)\right) \land \left(\left(\forall x \in \operatorname{Native}\left(q\right),\; \operatorname{eta}\left(q, hq, \operatorname{apply}\left(\operatorname{resetTheta}\left(q\right), x\right)\right) = \operatorname{multiply}\left(\operatorname{targetTime}\left(\operatorname{mod}\left(q, 4\right)\right), \operatorname{eta}\left(q, hq, x\right)\right)\right) \land \left(\left(\forall x \in \operatorname{Native}\left(q\right),\; \operatorname{eta}\left(q, hq, \operatorname{apply}\left(\operatorname{groupAction}\left(\operatorname{resetMatrix}\left(q\right), \operatorname{ofAdd}\left(true\right)\right), x\right)\right) = \operatorname{multiply}\left(\operatorname{targetLabel}\left(\operatorname{mod}\left(q, 4\right)\right), \operatorname{eta}\left(q, hq, x\right)\right)\right) \land \left(\left(\forall n \in Nat, v \in \operatorname{VertexModule}\left(Sign, q\right),\; \operatorname{eta}\left(q, hq, \operatorname{nativeStage}\left(q, n, v\right)\right) = \operatorname{arithmeticChart}\left(q, \operatorname{bProjection}\left(q, \operatorname{ringEquiv}\left(q, \operatorname{pp}\left(q, \operatorname{coordinatePolynomial}\left(resetLabel, q, \operatorname{apply}\left(\operatorname{power}\left(\operatorname{resetInverse}\left(q, hq\right), n\right), v\right)\right)\right)\right)\right)\right)\right) \land \left(\left(\forall p \in IntPolynomial,\; \operatorname{arithmeticChart}\left(q, \operatorname{squarePolynomial}\left(q, p\right)\right) = \operatorname{integerPolynomialEval}\left(p, \operatorname{targetTime}\left(\operatorname{mod}\left(q, 4\right)\right)\right)\right) \land \left(\operatorname{joint}\left(q\right) = \operatorname{idealSup}\left(\operatorname{principalIdeal}\left(\operatorname{residueF}\left(\operatorname{mod}\left(q, 4\right)\right)\right), \operatorname{principalIdeal}\left(H\right)\right) \land \left(\forall u \in \operatorname{Units}\left(\operatorname{Target}\left(\operatorname{mod}\left(q, 4\right)\right)\right),\; \exists n \in Nat,\; \operatorname{less}\left(n, \operatorname{targetBound}\left(\operatorname{mod}\left(q, 4\right)\right)\right) \land \left(\operatorname{power}\left(\operatorname{targetTimeUnit}\left(\operatorname{mod}\left(q, 4\right)\right), n\right) = u \land \operatorname{eta}\left(q, hq, \operatorname{apply}\left(\operatorname{rho}\left(q, hq, \operatorname{power}\left(\operatorname{unitShift}\left(\operatorname{ResetGraph}\left(q\right)\right), n\right)\right), \operatorname{generator}\left(q, hq\right)\right)\right) = \operatorname{unitValue}\left(u\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResetNativeIntegerChart.native_square_arithmetic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

H is X^2+1 and joint(q) is the sum of the principal ideals generated by F(q) and H. SquareRing(q) is Int[X]/joint(q). bProjection uses DoubleQuot.quotQuotEquivQuotSup and the second canonical quotient map; Ideal.map_span identifies its second ideal with the principal ideal generated by [H]. The original nativeSquare is id+Theta^2. A quotient-kernel witness b yields the actual native preimage Phi(b); a native preimage y yields the coefficient Phi inverse(y). These explicit witnesses identify the canonical projection kernel with the original range alone. nativeSquareEquiv is the resulting integer-linear quotient equivalence. nativeSquareRing explicitly transports multiplication and one through that equivalence; nativeArithmeticEquiv then gives the actual inverse ring chart. The theorem also checks the original quotient addition.

In Int[X]/(H), t^2=-1 and t^4=1. The four-term geometric sum is zero. Periodicity reduces S(q) to S(q mod 4), without division by X-1. Consequently F has residues 1,-2,1-2X,0 and W has residues 1-X,2+X,2X,-1. Both ideal inclusions for residue two use the integral certificates 5=4H+(2X+1)(1-2X), X-3=-3(1-2X)-5X, 1-2X=-2(X-3)-5, and H=(X-3)(X+3)+10.

Target(r), time and label are respectively ZMod(1),1,1 for r=0; literal MonoidAlgebra(ZMod(2),Sign),single oddTau 1,single oddTau 1 for r=1; ZMod(5),3,1 for r=2; GaussianInt,i,-1 for r=3. The binary inverse uses actual coefficient reduction and liftNCRingHom. Its two inverse equations are checked on integer coefficients and both Sign elements. The Gaussian inverse uses Zsqrtd.lift and both inverse equations are checked on i and polynomial generators. The five-chart reuses quotientSpanCXSubCAlgEquiv and Int.quotientSpanNatEquivZMod. The zero chart has both unique maps. RingEquiv preserves one, integer scalars, multiplication and inverse maps; integerPolynomialEval means eval2 with the integer cast and the displayed forward-time element. principalIdeal and idealSup denote literal integral ideals. The stage equation keeps the original inverse-time power before the coordinate polynomial.

The uniform integral period-four reduction identifies the joint ideal in every residue class. These ideal equalities determine the four arithmeticChart branches and hence the native projection eta and quotient equivalence nativeArithmeticEquiv. The normalized native chart connects the original time and coefficient operators to these integral polynomial quotients.

Every target unit is reached by the actual numbered-history shift at the normalized generator. The exponent bounds targetBound are 1,2,4,4 in residue order. Units are respectively {1}, {1,tau}, {1,3,4,2}, and {1,i,-1,-i}. In the binary group algebra, expansion in the two literal coefficients and the augmentation ring map force a unit's coefficient sum to be one. The two coefficient possibilities give exactly 1 or tau. For Gaussian units, the standard norm-one criterion gives a^2+b^2=1. Integer bounds restrict each coefficient to -1,0,1 and yield the four displayed possibilities. In ZMod(5) each unit has one of the four explicit powers of 3. The actual rho_unitShift equation, map_pow, and the polynomial action law transport these powers to the original native action. unitValue denotes the underlying ring element of a unit; the final power is the group power of the actual history shift. targetTimeUnit has value targetTime and literal inverse 1,tau,2,-i in residue order, and every target unit equals its bounded group power.

Application to the full native action. Write N=DimensionGroup(resetMatrix q), Theta=resetTheta q, e=generator q hq and Phi=nativeIntEquiv q hq. The ring B is literally Int[X]/(F(q)); its polynomial scalar extension is fp:Int[X]->B, with x=fp(X). N has its integer module structure. Put J=id+Theta^2, H=range(J), Q=N/H and pi=H.mkQ. Every product on Q in this application is transported through nativeSquareEquiv; no product on N is used.

Let C be the actual subring centralizer of Theta in End_Int(N), with (f*g)(v)=f(g(v)). Multiplication on B defines Psi(b)(Phi(c))=Phi(b*c). This is an oriented ring equivalence B->C, whose inverse is f->Phi.inverse(f(e)). Indeed LinearMap.ofAEval promotes a commuting integer-linear map to polynomial linearity. The surjectivity of Int[X]->B then makes it B-linear, so its value on 1 determines it on every vector. The chart fixes Psi(x)=Theta and Psi(1+x^2)=J. These constructions use the existing native_presentation and the standard polynomial-module and conjugation universal properties.

For an actual h in ResetFullAut q, membership in fullAutSubgroup says h*shift=shift*h. Apply multiplicativity of the actual full representation rho and rho_unitShift to obtain rho(h)*Theta=Theta*rho(h). The inverse commutes as well, by the unit inverse commutation law. Thus rho(h) is a unit of C. Define chi_B(h)=Psi.inverse(rho(h)) as a B-unit. It preserves one, multiplication and inverses and satisfies rho(h)(v)=Phi(chi_B(h)*Phi.inverse(v)) for every original native v. Its value is Phi.inverse(rho(h)(e)); the actual forward shift has value x. Evaluation at e proves uniqueness of the unit with this action law. Surjectivity of chi_B is not asserted.

Form the literal second quotient A=B/(1+x^2). Its canonical identification with SquareRing(q) is the double-quotient equivalence, using Ideal.map_span to identify the mapped square ideal. Composing with arithmeticChart identifies A with the displayed arithmetic target. Define chi_A by applying the canonical quotient B->A to chi_B, including its inverse. If eta_A is the corresponding native projection, then eta_A(rho(h)(v))=chi_A(h)*eta_A(v) for every v, eta_A(e)=1, and chi_A(h)=eta_A(rho(h)(e)). This proves uniqueness from the normalized generator and gives the exact induced action on the original quotient.

The canonical quotient time is Theta_bar=H.mapQ(H,Theta). Let C_bar be its actual centralizer subring in End_Int(Q). For f in C, the equality f*J=J*f preserves H. Define res(f)=H.mapQ(H,f). It satisfies res(f)(pi(v))=pi(f(v)), res(1)=1, res(f+g)=res(f)+res(g), and res(f*g)=res(f)*res(g), in the stated composition order. These equations also prove that the image commutes with Theta_bar. Thus res:C->C_bar is an actual unital ring homomorphism of End centralizers.

The native quotient chart identifies C_bar with A by the same polynomial-linearity argument. If Psi_bar is this scalar equivalence, then res(Psi(b))=Psi_bar(b mod (1+x^2)). Every scalar in A has a representative in B, so res is onto. Its kernel is exactly the image of L->J*L: res(f)=0 if and only if there exists L in C with f=J*L. The reverse witness comes from membership in the principal ideal generated by 1+x^2 in B and is transported by Psi. This argument uses neither cancellation by J nor lifting of arbitrary units.

Let d be 1,2,4,4 in residue order. The accepted unit classification gives exhaustion by the forward-time unit, and its exact arithmetic order is d: tau has order two in the binary ring, 3 has order four modulo five, and i has order four in the Gaussian ring. The zero-ring unit has order one. With these arithmetic hypotheses in place, pow_injOn_Iio_orderOf gives a unique exponent j with 0<=j<d for every target unit. Every A-unit has the actual history shift^j as a chi_A preimage. In particular chi_A is onto.

Every integer-linear automorphism of Q commuting with Theta_bar is exactly the action induced by one of these actual shift powers, with unique j in that interval. The induced actual forward shift has exact order d. For every integer-linear automorphism f of N commuting with Theta, there is likewise a unique j in that interval such that f-Theta^j=J*L for some L in C. This applies to every actual rho(h). The phase is unique; the correction factor L is only existential here. Its uniqueness is not asserted, including when q mod 4 is three.

The phase equation is equivalent both to pi(f(v))=pi(Theta^j(v)) for every native v and to eta(f(e))=targetTime^j at the normalized generator. At phase zero these give the exact all-vector and generator criteria for ker(chi_A). The first isomorphism theorem gives FullAut/ker(chi_A) isomorphic to A-units. Composing with zmodMulEquivOfGenerator gives the oriented equivalence with Multiplicative(ZMod d), carrying the class of the actual forward shift to 1 modulo d.

For q mod 4 equal to two, the canonical identification of eta with ZMod(5) is the literal clock resetFiveClock(resetNativeEquiv(v)). Its weights are exactly 1,2,0,4 in original vertex order, applied to the sum of the two integer Sign coefficients. The kernel equality reset_five_clock_image and the value one at the actual e0 fix the normalization. RingHom.ext_zmod makes the prime-ring identification unique. Original forward Theta multiplies this readout by 3. A native stage-n row is read after n inverse transitions, so its clock is 2^n times the clock of the row. These are the original forward and stage orientations.

At the same residue, q is even and the actual evenAut has rho(evenAut)=id+Theta by rho_even. Therefore its clock action on every vector is multiplication by 4=1+3. Since 3^2=4 modulo five, its unique phase is two, and rho(evenAut)-Theta^2=J*L for some actual native commuting endomorphism L. The action and phase statements retain the entire original history domain; no inertness or Sign-equivariance premise is imposed.

The chart is integral and includes q=1 directly. It assumes no parity, q>=2, field, nontriviality, rational Sign splitting, native R-linearity, cone preservation or history Sign-equivariance. The application above uses native_presentation, native_square_arithmetic, rho_unitShift, rho_even, reset_five_clock_image and the indicated standard universal properties. It does not require a nontrivial square quotient or injectivity of J. This is a repository synthesis of existing results and standard polynomial/module universal properties, without a literature novelty claim.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetNativeIntegerChart.arithmeticChart`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetNativeIntegerChart.eta`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetNativeIntegerChart.nativeArithmeticEquiv`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetNativeIntegerChart.nativeIntEquiv`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetNativeIntegerChart.nativePolynomialEquiv`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetNativeIntegerChart.native_presentation`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetNativeIntegerChart.native_square_arithmetic`
- Dependency: [D5/S3/ConceptDynamics/Coding/ResetFullStandardBeamRepresentation](ResetFullStandardBeamRepresentation.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/ResetSignIntegerCyclic](ResetSignIntegerCyclic.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/ResetSquareIntegralDefect](ResetSquareIntegralDefect.md)

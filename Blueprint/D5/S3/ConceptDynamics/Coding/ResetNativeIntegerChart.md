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

The chart is integral and includes q=1 directly. It assumes no parity, q>=2, field, nontriviality, rational Sign splitting, native R-linearity, cone preservation or history Sign-equivariance. The actual End-ring centralizer, full B-unit character, square-character scalar law and surjectivity, its kernel quotient, the unique native shift phase, and literal five-clock identification remain obligations beyond this arithmetic theorem. Surjectivity of the B-unit character is not asserted. This is a repository synthesis of existing results and standard polynomial/module universal properties, without a literature novelty claim.

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

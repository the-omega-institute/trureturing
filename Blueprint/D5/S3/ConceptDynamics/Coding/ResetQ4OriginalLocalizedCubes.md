# Dyadic cube factorization of the original reset action

## Abstract

Dyadic Bezout gluing transports original quartic unit cube forms to every original history automorphism.

**Theorem 1.1 (The centralizer time unit has the literal forward matrix value).**

Lean statement: `D5/S3/ConceptDynamics/Coding/ResetQ4OriginalLocalizedCubes.time_val`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResetQ4OriginalLocalizedCubes.time_val` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual time element of Centralizer has matrix value exactly T after subtype and unit coercions. T is the original forward column transition. The character construction and symbolic time evaluation use this precise value.

**Theorem 1.2 (The second centralizer unit has value exactly one plus T).**

Lean statement: `D5/S3/ConceptDynamics/Coding/ResetQ4OriginalLocalizedCubes.onePlusTime_val`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResetQ4OriginalLocalizedCubes.onePlusTime_val` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The fixed second centralizer unit has matrix value 1+T in the same original vertex coordinates. This identifies the forward factor in its symbolic signed evaluation; its backward factor is a separate calculation.

**Theorem 1.3 (The actual original image evaluates to rhoD).**

Lean statement: `D5/S3/ConceptDynamics/Coding/ResetQ4OriginalLocalizedCubes.originalImage_val`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResetQ4OriginalLocalizedCubes.originalImage_val` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every h : ResetFullAut 4, the matrix value of originalImage h equals rhoD h, the scalar-extended original beam-set-image action. This identifies the same action in two realizations and asserts no surjectivity onto the matrix centralizer.

Let D=Int[1/2] and index matrices by the eight original signed vertices Sigma (_:Fin 4), Sign. The actual full group is ResetFullAut(4). Transport its original beam-set-image action rho through resetNativeEquiv to the original vertex module, take its column matrix, and extend coefficients from Int to D; this defines rhoD. T is the column matrix of the literal forward reset transition, with the same scalar extension. It is the transpose of the expanded row adjacency. The original unit shift has image T, and the original evenAut(4) has image I+T.

Write f=X^4-X^3-X^2-X-1, g=X^4+X^3+X^2+X+1, and F=f*g. The integral certificate X*f+(2-X)*g=2 gives (X/2)*f+(1-X/2)*g=1 over D. Thus the original quotient D[X]/(F) is isomorphic to D[X]/(f) times D[X]/(g). The two projectors are (1-X/2)*g and (X/2)*f. Monic representatives give the inverse map. Component units and their inverses glue together without any residue compatibility requirement on the chosen roots.

For each actual h, the published scalarUnit construction gives an integral unit u_h in Int[X]/(F), from the action rho(h) and its inverse. Its components are compatible modulo two. ResetQ4UnitCubes supplies u_plus=alpha^i*Bplus^j*v^3 and u_minus=Bminus^k*w^3 with i,j,k in Fin 3. Compatibility forces j=k. Time has components (alpha,beta), while I+time has components (Bplus,Bminus). Since beta^5=1, replacing w by beta^(3*i)*w gives beta^i*(beta^(3*i)*w)^3=w^3. This exact correction aligns the two component forms before the preserved original applications are glued.

The cyclic integral chart and the original vertex basis identify multiplication by X with forward T. Polynomial ring-hom extensionality then gives F(T)=0 and the evaluation identity for every integral scalar, including u_h. Evaluation descends from D[X]/(F) to the original matrix ring. Evaluating a glued unit also evaluates its actual inverse, and commutativity of the source proves that its matrix commutes with T. Centralizer is the subgroup of matrix units centralizing the unit with matrix value T.

**Theorem 1.4 (Every original automorphism has a commuting dyadic cube factorization).**

$$\forall h \in \operatorname{ResetFullAut}\left(4\right),\; \exists i \in \operatorname{Fin}\left(3\right), j \in \operatorname{Fin}\left(3\right), v \in Centralizer,\; \operatorname{rhoD}\left(h\right) = \operatorname{pow}\left(T, \operatorname{val}\left(i\right)\right) \cdot \operatorname{pow}\left(1 + T, \operatorname{val}\left(j\right)\right) \cdot \operatorname{pow}\left(\operatorname{matrixValue}\left(v\right), 3\right) \land \operatorname{Commute}\left(\operatorname{matrixValue}\left(v\right), T\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResetQ4OriginalLocalizedCubes.original_localized_cube_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The matrix V is a genuine unit over D and commutes with the literal forward T. The proof factors the actual integral scalar unit, then evaluates the factorization in the original action diagram. The bounded exponents are representatives modulo three; no uniqueness of them or of the cube root is asserted.

The cube factorization constrains every actual original image and asserts no surjectivity onto the matrix-unit centralizer or presentation of the full original group. Given a separately supplied additive character of the full matrix-unit centralizer with values in ZMod(3) that kills the original shift, a cube contributes zero and each original image has character value j times the value at I+T. This conditional application requires that character as a hypothesis; it does not construct one for an arbitrary dyadic centralizer.

The following is the original application checked in the preserved complete proof and type at revision 95de10d7dfdf708bf857fa2f2bac3356a044b08a. Let G=ResetGraph 4, hG=Alternating.reset_expanded_essential 4, P=ResponseTwoSidedConsumer.original G hG, and tau=StandardBeamHomeomorphisms.unitShift G, the literal forward shift. For every f:ResetFullAut 4, psi(f) is Units.map (ResetIntegralGluing.rplus 4).toMonoidHom applied to Units.map (ResetIntegralGluing.plus 4).toMonoidHom applied to ResetNativeUnitNormalForm.scalarUnit 4 (by decide) (ResetFullStandardBeamRepresentation.rho 4 (by decide) f) (ResetHistoryKernel.rho_time 4 (by decide) f). This is the actual integral scalar of the same native action.

Put c=ResetQ4UnitCubes.residueCharacter and t=psi(tau). In the integral chart, originalScalar_action, rho_unitShift and native_presentation identify the scalar of tau with fp 4 X, whose plus image is alpha. Applying residueCharacter_plus_factorization to alpha with exponents 1,0 and cube witness 1 gives c(Additive.ofMul t)=0. Subgroup.zpowers_le then gives hker:Subgroup.zpowers t ≤ c.toMultiplicativeRight.ker. Define q=(QuotientGroup.lift (Subgroup.zpowers t) c.toMultiplicativeRight hker).toAdditiveLeft and chi_add(f)=q(Additive.ofMul ((QuotientGroup.mk' (Subgroup.zpowers t)) (psi(f)))). Its domain before composition is exactly Additive ((ResetIntegralGluing.Common 4)ˣ ⧸ Subgroup.zpowers t). By the quotient lift computation, chi_add(f)=c(Additive.ofMul (psi(f))). This is the same native character used in the preserved application.

For that same f, localized_normal_form applied to its originalScalar supplies shared i,j:Fin 3 and a genuine localized unit. Apply evaluateCentralizer to its factorization and retain its residue clause: for v in the actual centralizer, originalImage f=time^i.val * onePlusTime^j.val * v^3 and chi_add(f)=(j.val:ZMod 3). The signed evaluation identities gamma_time_signed_evaluation and gamma_onePlus_signed_evaluation identify the integerGyrationValue inputs as the original ordered adjacency A with I, and I+A with its actual signed factor S. The preserved application evaluates periods three and six as -4,-35 for (A,I) and -8,-53 for (I+A,S). Their sums are -39=0 and -61=2 modulo three. These numerical evaluations belong to the archived application; they are not separate canonical numerical declarations. Homomorphism laws kill v^3 and give Multiplicative.toAdd (Gamma (originalImage f))=2*j.val. Since 2*2=1 in ZMod 3, chi_add(f)=2*Multiplicative.toAdd (Gamma (originalImage f)).

For every h:ResetFullAut 4, fullAut_has_two_windows supplies a,b,c,d for h and its actual inverse. The general OriginalResponseTableIntake constructs the actual tables and SameTableConjugacy. OriginalPositiveWordAssembly.positive_word then gives a positive Word w on the original presentation with h(x)=time(s,w.eval(x)) for every original legal history, where s=-a-((a+c)+(b+d+1)); its complete letter-count clause remains part of that theorem. word_rebased returns the actual endpoint unit U. The signed cut action at stage zero, endpointMap_cast, inverse_time_order and originalRows_mul identify rhoD(h)=(tau^(-1))^N*U, with N=a+((a+c)+(b+d+1)) and s=-N. Equality of units transports the inverse and the backward factor too.

For every natural p with NeZero p and hp:3 divides p, corrected_localized_word gives the reduced history cochain of that same h and w. PresentationTimeCochain.time_calibration identifies the actual time term as card(Orbit P p), and SourceOnly.CentralizerTimePowers.translated_value supplies its signed integer-power contribution on the matrix side. Combining them gives ZMod.castHom hp (ZMod 3) (historyGyration h p)=Multiplicative.toAdd (gamma p hp (originalImage h)). This holds for all positive three-divisible periods before selecting three and six, using both factors and the same original h.

The preserved application computes original forward fixed-point counts 0,2,6,50 at periods 1,2,3,6. Divisor decomposition gives primitive-point counts 0,2,6,42 and hence primitive-orbit counts two at period three and seven at period six. Their sum is zero in ZMod 3, so the periodwise signed time ambiguities cancel. With g_p=historyGyration h p and red6=reduceSix, the identity is chi_add(h)=2*(g_3+red6(g_6))=2*Multiplicative.toAdd (Gamma (originalImage h)). Letter count is never substituted for signed time.

If h and k agree on the literal subtype {x:ResetHistory 4 // (shift (ResetGraph 4))^[6] x=x}, every true primitive period-three history belongs to it by applying its forward period equality twice, and every primitive period-six history also belongs. historyGyration_congr_on_primitive identifies both terms of the same chi_add, so this character factors through the literal forward Fix6 restriction on original histories. The preserved application identifies this exact public quotient-lift readout with the private character in ResetQ4SmallPeriodRefutation.claim and applies its existing result to the joint periods one through five. Factorization through any individual natural n with 0<n<6 would give factorization through that joint restriction by projection to i=n-1 in Fin 5, contradicting the result. Every such n is therefore excluded for this same native character.

These consequences concern the original history action, with the exact native quotient character and its fixed residue orientation. They make no rho-surjectivity assertion, no assertion that arbitrary centralizer units are native actions, no presentation of the full group, and no physical, resource or literature-novelty claim.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetQ4OriginalLocalizedCubes.onePlusTime_val`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetQ4OriginalLocalizedCubes.originalImage_val`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetQ4OriginalLocalizedCubes.original_localized_cube_factorization`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetQ4OriginalLocalizedCubes.time_val`
- Dependency: [D5/S3/ConceptDynamics/Coding/ResetNativeUnitNormalForm](ResetNativeUnitNormalForm.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/ResetQ4UnitCubes](ResetQ4UnitCubes.md)

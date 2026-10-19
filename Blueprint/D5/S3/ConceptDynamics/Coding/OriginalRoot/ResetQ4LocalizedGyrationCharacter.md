# The fixed localized character on the original reset action

## Abstract

The original reset column action carries the fixed localized gyration character and symbolic signed evaluations.

The character is constructed on the actual centralizer of the original forward column transition. Its symbolic evaluations identify the exact signed factors; the original-action application also uses the numerical calibrations and the periodic-action comparison described below.

The fixed polynomial is rationalGyrationPolynomial n m d from CountedGyrationPolynomial, with signed integer value signedGyrationLift and its matrix-pair definition integerGyrationValue from CountedPositiveTriangleLocalizedConsumer. CountedSignedGyrationEvaluator supplies a separate evaluation adapter for that same value. canonicalLocalizedGyration evaluates that same integer-valued polynomial at strictly positive representatives of a reduction modulo 3^(e+1), then reduces its integer value to ZMod 3. The dyadic specialization uses e = padicValInt 3 ((2*d)!) and gyrationDyadicReduction d. canonicalLocalizedGyration_signed_agreement uses the explicit integral numerator clearing (2*d)! and allows both signed input matrices, including zeros. A separately chosen cochain or period-specific polynomial is not substituted.

**Definition 1.1 (Dyadic coefficients).**

Lean statement: `D5/S3/ConceptDynamics/Coding/OriginalRoot/ResetQ4LocalizedGyrationCharacter.Dyadic`

*Formalization.* `D5/S3/ConceptDynamics/Coding/OriginalRoot/ResetQ4LocalizedGyrationCharacter.Dyadic` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Dyadic is the existing localization GyrationDyadic = Z[1/2]; this abbreviation supplies no new ring or theorem.

**Definition 1.2 (The original eight vertices).**

Lean statement: `D5/S3/ConceptDynamics/Coding/OriginalRoot/ResetQ4LocalizedGyrationCharacter.Vertex`

*Formalization.* `D5/S3/ConceptDynamics/Coding/OriginalRoot/ResetQ4LocalizedGyrationCharacter.Vertex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Vertex is exactly ResetQ4OriginalLocalizedCubes.VertexIndex, the original signed vertices indexed by Fin 4 and the two signs.

**Definition 1.3 (Original column matrices).**

Lean statement: `D5/S3/ConceptDynamics/Coding/OriginalRoot/ResetQ4LocalizedGyrationCharacter.OriginalMatrix`

*Formalization.* `D5/S3/ConceptDynamics/Coding/OriginalRoot/ResetQ4LocalizedGyrationCharacter.OriginalMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

OriginalMatrix is the existing DyadicMatrix on Vertex. The original action and literal forward transition use the column convention.

**Definition 1.4 (The full matrix unit centralizer).**

Lean statement: `D5/S3/ConceptDynamics/Coding/OriginalRoot/ResetQ4LocalizedGyrationCharacter.Centralizer`

*Formalization.* `D5/S3/ConceptDynamics/Coding/OriginalRoot/ResetQ4LocalizedGyrationCharacter.Centralizer` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Centralizer is the existing subgroup of units in OriginalMatrix centralizing the original time unit. It is not asserted to be the image of ResetFullAut 4.

**Definition 1.5 (The fixed enumeration).**

Lean statement: `D5/S3/ConceptDynamics/Coding/OriginalRoot/ResetQ4LocalizedGyrationCharacter.vertexAt`

*Formalization.* `D5/S3/ConceptDynamics/Coding/OriginalRoot/ResetQ4LocalizedGyrationCharacter.vertexAt` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For k in Fin 8, vertexAt k has first index k.val / 2 and sign Multiplicative.ofAdd (decide (k.val % 2 = 1)). Thus the order is (0,false),(0,true),...,(3,true). It is not an arbitrarily chosen enumeration.

**Definition 1.6 (The enumeration equivalence).**

Lean statement: `D5/S3/ConceptDynamics/Coding/OriginalRoot/ResetQ4LocalizedGyrationCharacter.vertexEquiv`

*Formalization.* `D5/S3/ConceptDynamics/Coding/OriginalRoot/ResetQ4LocalizedGyrationCharacter.vertexEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

vertexEquiv is Equiv.ofBijective of this exact vertexAt and its finite bijectivity proof; no orientation is changed.

**Definition 1.7 (Reindex and transpose the column matrix).**

Lean statement: `D5/S3/ConceptDynamics/Coding/OriginalRoot/ResetQ4LocalizedGyrationCharacter.originalRows`

*Formalization.* `D5/S3/ConceptDynamics/Coding/OriginalRoot/ResetQ4LocalizedGyrationCharacter.originalRows` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every coefficient type R and every Vertex-square matrix M, originalRows M i j = M (vertexEquiv j) (vertexEquiv i). Both the transpose and the explicit order are part of this definition.

**Theorem 1.8 (The row representation reverses products).**

Lean statement: `D5/S3/ConceptDynamics/Coding/OriginalRoot/ResetQ4LocalizedGyrationCharacter.originalRows_mul`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/OriginalRoot/ResetQ4LocalizedGyrationCharacter.originalRows_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every type R with CommSemiring R and all Vertex-square matrices M,N, originalRows (M*N) = originalRows N * originalRows M. The order reversal is essential. This consumed helper expresses ordinary matrix transpose and equivalence reindexing; it is not claimed as new matrix algebra.

**Theorem 1.9 (The original identity in row coordinates).**

Lean statement: `D5/S3/ConceptDynamics/Coding/OriginalRoot/ResetQ4LocalizedGyrationCharacter.originalRows_one`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/OriginalRoot/ResetQ4LocalizedGyrationCharacter.originalRows_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every type R with Semiring R, originalRows (1 : Matrix Vertex Vertex R) = 1. Commutativity is not assumed. Trivial semirings remain included. This consumed identity helper is not an independent mathematical endpoint.

**Definition 1.10 (The literal forward row adjacency).**

Lean statement: `D5/S3/ConceptDynamics/Coding/OriginalRoot/ResetQ4LocalizedGyrationCharacter.originalAdjacency`

*Formalization.* `D5/S3/ConceptDynamics/Coding/OriginalRoot/ResetQ4LocalizedGyrationCharacter.originalAdjacency` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The integer matrix A has A i j = 1 exactly when (j.val / 2 = 0 and j.val % 2 differs from i.val % 2), or (j.val / 2 = i.val / 2 + 1 and the parities agree); otherwise it is zero. Under the integer embedding into Z[1/2], A is originalRows T for the literal original forward column transition T. It is not inverse time.

**Definition 1.11 (The signed factor for this I+T).**

Lean statement: `D5/S3/ConceptDynamics/Coding/OriginalRoot/ResetQ4LocalizedGyrationCharacter.onePlusSignedFactor`

*Formalization.* `D5/S3/ConceptDynamics/Coding/OriginalRoot/ResetQ4LocalizedGyrationCharacter.onePlusSignedFactor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Write S for the exact eight rows [0,0,1,0,-1,0,1,0]; [0,0,0,1,0,-1,0,1]; [0,1,0,-1,1,1,-1,-1]; [1,0,-1,0,1,1,-1,-1]; [0,0,0,0,0,0,1,0]; [0,0,0,0,0,0,0,1]; [0,1,0,-1,0,1,0,-1]; [1,0,-1,0,1,0,-1,0]. The private certificate states (I+A)(I-S)=(I-S)(I+A)=I and A(I-S)=(I-S)A=S. Consequently S represents originalRows ((I+T)^(-1)*T), not the inverse alone. Zero and negative entries are retained.

**Definition 1.12 (The same row cochain on original columns).**

Lean statement: `D5/S3/ConceptDynamics/Coding/OriginalRoot/ResetQ4LocalizedGyrationCharacter.columnGyration`

*Formalization.* `D5/S3/ConceptDynamics/Coding/OriginalRoot/ResetQ4LocalizedGyrationCharacter.columnGyration` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural d with NeZero d and all OriginalMatrix M,N, columnGyration d M N = dyadicGyration d (originalRows M) (originalRows N). Divisibility by three is not part of this definition; it is required for the triangle and character laws.

**Theorem 1.13 (The correctly oriented column triangle).**

Lean statement: `D5/S3/ConceptDynamics/Coding/OriginalRoot/ResetQ4LocalizedGyrationCharacter.columnGyration_triangle`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/OriginalRoot/ResetQ4LocalizedGyrationCharacter.columnGyration_triangle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural d with NeZero d, a proof hd : 3 divides d, and arbitrary OriginalMatrix R,U,V, the exact identity is columnGyration d R (U*V) + columnGyration d U (V*R) = columnGyration d (R*U) V. No positivity, invertibility or nonzero-entry hypothesis is imposed on these matrices. The row triangle is instantiated at (originalRows U, originalRows R, originalRows V) and product reversal gives this column orientation.

**Definition 1.14 (The constructed centralizer character).**

Lean statement: `D5/S3/ConceptDynamics/Coding/OriginalRoot/ResetQ4LocalizedGyrationCharacter.gamma`

*Formalization.* `D5/S3/ConceptDynamics/Coding/OriginalRoot/ResetQ4LocalizedGyrationCharacter.gamma` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each natural d with NeZero d and hd : 3 divides d, gamma d hd is a monoid homomorphism from Centralizer to Multiplicative (ZMod 3). Its additive value at a unit U is columnGyration d U (U^(-1)*T), using underlying original column matrices. The triangle and commutation with T prove the homomorphism laws. Multiplicative encodes addition of ZMod 3; no arbitrary supplied chi occurs here.

**Definition 1.15 (The combined period three and six character).**

Lean statement: `D5/S3/ConceptDynamics/Coding/OriginalRoot/ResetQ4LocalizedGyrationCharacter.Gamma`

*Formalization.* `D5/S3/ConceptDynamics/Coding/OriginalRoot/ResetQ4LocalizedGyrationCharacter.Gamma` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Gamma is exactly gamma 3 (by decide) * gamma 6 (by decide), the pointwise product of these homomorphisms. In additive notation its value is the sum of their values in ZMod 3. This definition alone supplies no numeric calibration.

**Theorem 1.16 (The symbolic evaluation at original time).**

Lean statement: `D5/S3/ConceptDynamics/Coding/OriginalRoot/ResetQ4LocalizedGyrationCharacter.gamma_time_signed_evaluation`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/OriginalRoot/ResetQ4LocalizedGyrationCharacter.gamma_time_signed_evaluation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every d : Nat with NeZero d and hd : 3 divides d, Multiplicative.toAdd (gamma d hd time) = (integerGyrationValue d originalAdjacency 1 : ZMod 3). Here time is exactly ResetQ4OriginalLocalizedCubes.time. The second factor is I because time^(-1)*T=I. This identity does not evaluate the integer expression to a numeral.

**Theorem 1.17 (The symbolic signed evaluation at I+time).**

Lean statement: `D5/S3/ConceptDynamics/Coding/OriginalRoot/ResetQ4LocalizedGyrationCharacter.gamma_onePlus_signed_evaluation`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/OriginalRoot/ResetQ4LocalizedGyrationCharacter.gamma_onePlus_signed_evaluation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every d : Nat with NeZero d and hd : 3 divides d, Multiplicative.toAdd (gamma d hd onePlusTime) = (integerGyrationValue d (1+originalAdjacency) onePlusSignedFactor : ZMod 3). Here onePlusTime is exactly ResetQ4OriginalLocalizedCubes.onePlusTime. The anti-multiplicative originalRows identity and the private inverse certificate identify the signed second factor. Agreement at strictly positive entries alone would not justify its negative entries and zeros.

The following is the original application checked in the preserved complete proof and type at revision 95de10d7dfdf708bf857fa2f2bac3356a044b08a. Let G=ResetGraph 4, hG=Alternating.reset_expanded_essential 4, P=ResponseTwoSidedConsumer.original G hG, and tau=StandardBeamHomeomorphisms.unitShift G, the literal forward shift. For every f:ResetFullAut 4, psi(f) is Units.map (ResetIntegralGluing.rplus 4).toMonoidHom applied to Units.map (ResetIntegralGluing.plus 4).toMonoidHom applied to ResetNativeUnitNormalForm.scalarUnit 4 (by decide) (ResetFullStandardBeamRepresentation.rho 4 (by decide) f) (ResetHistoryKernel.rho_time 4 (by decide) f). This is the actual integral scalar of the same native action.

Put c=ResetQ4UnitCubes.residueCharacter and t=psi(tau). In the integral chart, originalScalar_action, rho_unitShift and native_presentation identify the scalar of tau with fp 4 X, whose plus image is alpha. Applying residueCharacter_plus_factorization to alpha with exponents 1,0 and cube witness 1 gives c(Additive.ofMul t)=0. Subgroup.zpowers_le then gives hker:Subgroup.zpowers t ≤ c.toMultiplicativeRight.ker. Define q=(QuotientGroup.lift (Subgroup.zpowers t) c.toMultiplicativeRight hker).toAdditiveLeft and chi_add(f)=q(Additive.ofMul ((QuotientGroup.mk' (Subgroup.zpowers t)) (psi(f)))). Its domain before composition is exactly Additive ((ResetIntegralGluing.Common 4)ˣ ⧸ Subgroup.zpowers t). By the quotient lift computation, chi_add(f)=c(Additive.ofMul (psi(f))). This is the same native character used in the preserved application.

For that same f, localized_normal_form applied to its originalScalar supplies shared i,j:Fin 3 and a genuine localized unit. Apply evaluateCentralizer to its factorization and retain its residue clause: for v in the actual centralizer, originalImage f=time^i.val * onePlusTime^j.val * v^3 and chi_add(f)=(j.val:ZMod 3). The signed evaluation identities gamma_time_signed_evaluation and gamma_onePlus_signed_evaluation identify the integerGyrationValue inputs as the original ordered adjacency A with I, and I+A with its actual signed factor S. The preserved application evaluates periods three and six as -4,-35 for (A,I) and -8,-53 for (I+A,S). Their sums are -39=0 and -61=2 modulo three. These numerical evaluations belong to the archived application; they are not separate canonical numerical declarations. Homomorphism laws kill v^3 and give Multiplicative.toAdd (Gamma (originalImage f))=2*j.val. Since 2*2=1 in ZMod 3, chi_add(f)=2*Multiplicative.toAdd (Gamma (originalImage f)).

For every h:ResetFullAut 4, fullAut_has_two_windows supplies a,b,c,d for h and its actual inverse. The general OriginalResponseTableIntake constructs the actual tables and SameTableConjugacy. OriginalPositiveWordAssembly.positive_word then gives a positive Word w on the original presentation with h(x)=time(s,w.eval(x)) for every original legal history, where s=-a-((a+c)+(b+d+1)); its complete letter-count clause remains part of that theorem. word_rebased returns the actual endpoint unit U. The signed cut action at stage zero, endpointMap_cast, inverse_time_order and originalRows_mul identify rhoD(h)=(tau^(-1))^N*U, with N=a+((a+c)+(b+d+1)) and s=-N. Equality of units transports the inverse and the backward factor too.

For every natural p with NeZero p and hp:3 divides p, corrected_localized_word gives the reduced history cochain of that same h and w. PresentationTimeCochain.time_calibration identifies the actual time term as card(Orbit P p), and SourceOnly.CentralizerTimePowers.translated_value supplies its signed integer-power contribution on the matrix side. Combining them gives ZMod.castHom hp (ZMod 3) (historyGyration h p)=Multiplicative.toAdd (gamma p hp (originalImage h)). This holds for all positive three-divisible periods before selecting three and six, using both factors and the same original h.

The preserved application computes original forward fixed-point counts 0,2,6,50 at periods 1,2,3,6. Divisor decomposition gives primitive-point counts 0,2,6,42 and hence primitive-orbit counts two at period three and seven at period six. Their sum is zero in ZMod 3, so the periodwise signed time ambiguities cancel. With g_p=historyGyration h p and red6=reduceSix, the identity is chi_add(h)=2*(g_3+red6(g_6))=2*Multiplicative.toAdd (Gamma (originalImage h)). Letter count is never substituted for signed time.

If h and k agree on the literal subtype {x:ResetHistory 4 // (shift (ResetGraph 4))^[6] x=x}, every true primitive period-three history belongs to it by applying its forward period equality twice, and every primitive period-six history also belongs. historyGyration_congr_on_primitive identifies both terms of the same chi_add, so this character factors through the literal forward Fix6 restriction on original histories. The preserved application identifies this exact public quotient-lift readout with the private character in ResetQ4SmallPeriodRefutation.claim and applies its existing result to the joint periods one through five. Factorization through any individual natural n with 0<n<6 would give factorization through that joint restriction by projection to i=n-1 in Fin 5, contradicting the result. Every such n is therefore excluded for this same native character.

These consequences concern the original history action, with the exact native quotient character and its fixed residue orientation. They make no rho-surjectivity assertion, no assertion that arbitrary centralizer units are native actions, no presentation of the full group, and no physical, resource or literature-novelty claim.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/OriginalRoot/ResetQ4LocalizedGyrationCharacter.Centralizer`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/OriginalRoot/ResetQ4LocalizedGyrationCharacter.Dyadic`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/OriginalRoot/ResetQ4LocalizedGyrationCharacter.Gamma`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/OriginalRoot/ResetQ4LocalizedGyrationCharacter.OriginalMatrix`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/OriginalRoot/ResetQ4LocalizedGyrationCharacter.Vertex`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/OriginalRoot/ResetQ4LocalizedGyrationCharacter.columnGyration`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/OriginalRoot/ResetQ4LocalizedGyrationCharacter.columnGyration_triangle`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/OriginalRoot/ResetQ4LocalizedGyrationCharacter.gamma`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/OriginalRoot/ResetQ4LocalizedGyrationCharacter.gamma_onePlus_signed_evaluation`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/OriginalRoot/ResetQ4LocalizedGyrationCharacter.gamma_time_signed_evaluation`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/OriginalRoot/ResetQ4LocalizedGyrationCharacter.onePlusSignedFactor`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/OriginalRoot/ResetQ4LocalizedGyrationCharacter.originalAdjacency`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/OriginalRoot/ResetQ4LocalizedGyrationCharacter.originalRows`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/OriginalRoot/ResetQ4LocalizedGyrationCharacter.originalRows_mul`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/OriginalRoot/ResetQ4LocalizedGyrationCharacter.originalRows_one`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/OriginalRoot/ResetQ4LocalizedGyrationCharacter.vertexAt`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/OriginalRoot/ResetQ4LocalizedGyrationCharacter.vertexEquiv`
- Dependency: [D5/S3/ConceptDynamics/Coding/CountedLocalizedGyrationResidue](../CountedLocalizedGyrationResidue.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/ResetQ4OriginalLocalizedCubes](../ResetQ4OriginalLocalizedCubes.md)

# Positive Perron trace of original Reset beams

## Abstract

Positive Perron trace of original Reset beams.

**Definition 1.1 (The normalized native Perron trace).**

Lean statement: `D5/S3/ConceptDynamics/Coding/ResetPerronBeamTrace.tau`

*Formalization.* `D5/S3/ConceptDynamics/Coding/ResetPerronBeamTrace.tau` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural q with hq:2<=q, beta q=dbonacciPerronRoot q, p=(beta q)^(-1), and weight q i=suffixWeight q p i=sum over a<q-i.val of p^(a+1). rowWeight v=sum over (i,g):Fin q x Sign of cast(v(i,g))*weight q i. Both absolute Sign labels have equal weights. tau q hq is an Int-linear map from the original DimensionGroup(resetMatrix q) to Real. It is the actual Module.DirectLimit.lift of beta^(-(N:Int))*rowWeight at stage N, composed with the inverse of resetRowLimitEquiv, which transports both coefficients at the same stage.

**Theorem 1.2 (Right-row compatibility).**

Lean statement: `D5/S3/ConceptDynamics/Coding/ResetPerronBeamTrace.rowWeight_transition`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResetPerronBeamTrace.rowWeight_transition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every q:Nat with 2<=q and every v:Fin q x Sign -> Int, rowWeight q (rowTransition (ResetGraph q) v)=beta q * rowWeight q v. This is v -> v B for the actual numbered expanded adjacency. matrix_coefficient gives reset to (0,g*tau) and legal increment to (i+1,g). The suffix recurrence and weight zero=1 prove B r=beta r. No transpose is introduced.

**Theorem 1.3 (Every original natural stage).**

Lean statement: `D5/S3/ConceptDynamics/Coding/ResetPerronBeamTrace.tau_stage`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResetPerronBeamTrace.tau_stage` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every q:Nat, hq:2<=q, N:Nat and v:VertexModule Sign q, tau q hq (nativeStage q N v)=beta q^(-(N:Int))*sum over i:Fin q and g:Sign of cast((v i).coeff g)*weight q i. The native stage is the original same-stage colimit map. DirectLimit.lift_of and resetRowLimitEquiv_stage give the formula. Compatibility is beta^(-j)*beta^(j-i)=beta^(-i) for i<=j.

**Theorem 1.4 (Every lawful integer cut).**

Lean statement: `D5/S3/ConceptDynamics/Coding/ResetPerronBeamTrace.tau_beam_atCut`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResetPerronBeamTrace.tau_beam_atCut` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every q:Nat, hq:2<=q, U:Beam(ResetGraph q), m:Int and hm:AtCut(ResetGraph q) U.val m, hm.1 supplies Finite Parts and Fintype.ofFinite supplies its sum. Then tau q hq (resetBeamCoordinate q U)=beta q^(-m)*sum over P:Parts(ResetGraph q) U.val m of weight q (RayAt.endpoint (ResetGraph q) P.val).1. Parts consists of actual ray sets, with finite union and disjointness supplied by the original geometry. Distinct pasts sharing an endpoint count separately. coordinateAt_refine and endpointRow_refine use the Sigma of each earlier part and its numbered continuations. Their B^r advancement cancels the inverse-stage factor. intStage m is stage m.toNat after T^((-m).toNat); this includes negative cuts.

**Theorem 1.5 (Strictness detects beam nonemptiness).**

Lean statement: `D5/S3/ConceptDynamics/Coding/ResetPerronBeamTrace.tau_beam_positive`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResetPerronBeamTrace.tau_beam_positive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every q:Nat, hq:2<=q and actual beam U, 0<=tau q hq (resetBeamCoordinate q U), and 0<tau q hq (resetBeamCoordinate q U) if and only if U.val.Nonempty. All suffix weights are bounded below by the positive reciprocal Parry root. A point x in U determines the intrinsic part rayAt x m by saturation. Conversely each part is nonempty by RayAt.nonempty. The finite positive sum detects nonemptiness, including zero trace on the empty beam.

**Theorem 1.6 (Forward time).**

Lean statement: `D5/S3/ConceptDynamics/Coding/ResetPerronBeamTrace.tau_theta`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResetPerronBeamTrace.tau_theta` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every q:Nat, hq:2<=q and x in the original native DimensionGroup, tau q hq (resetTheta q x)=beta q*tau q hq x. rho_unitShift identifies forward resetTheta with the actual unit left shift. Forward time has factor beta while stage N has factor beta^(-N).

**Theorem 1.7 (Actual absolute Sign).**

Lean statement: `D5/S3/ConceptDynamics/Coding/ResetPerronBeamTrace.tau_sign`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResetPerronBeamTrace.tau_sign` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every q:Nat, hq:2<=q and native x, tau q hq (groupAction(resetMatrix q)(Multiplicative.ofAdd true) x)=tau q hq x. Reindexing the actual two absolute Sign coefficients proves this. No arbitrary history automorphism is assumed Sign-equivariant.

**Theorem 1.8 (The literal stage-zero basis ray).**

Lean statement: `D5/S3/ConceptDynamics/Coding/ResetPerronBeamTrace.tau_one`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResetPerronBeamTrace.tau_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every q:Nat with hq:2<=q, tau q hq (nativeIntEquiv q (0<q) 1)=1. generatorRay is resetRayBeam of resetBasisHistory at (suffix zero,absolute identity Sign) and cut zero. native_presentation identifies Phi(1) with nativeStage zero e0. e0 is exactly this literal vertex. vertexHistory_endpoint and resetBeamCoordinate_ray identify its ray coordinate. The zero-suffix weight is one. The inverse native chart is never asserted coordinatewise positive.

**Theorem 1.9 (Every original full history image).**

Lean statement: `D5/S3/ConceptDynamics/Coding/ResetPerronBeamTrace.original_action_positive`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResetPerronBeamTrace.original_action_positive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every q:Nat, hq:2<=q and h:ResetFullAut q, 0<tau q hq (rho q (0<q) h (nativeIntEquiv q (0<q) 1)). h ranges over all original history homeomorphisms commuting with unit shift. fullAut_has_two_windows derives both finite windows; image_ray_atCut makes the literal image of generatorRay finite at cut d. alpha=resetBasisHistory belongs to its own ray, so h(alpha) explicitly witnesses nonemptiness of its Set.image. rho_beam_image identifies that beam coordinate with the native action. The intrinsic finite Parts formula and beam strictness give positivity without a cone premise, normal form, marker hypothesis or full-shift surrogate.

**Theorem 1.10 (Negative scalar identity is excluded).**

Lean statement: `D5/S3/ConceptDynamics/Coding/ResetPerronBeamTrace.rho_ne_neg_id`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResetPerronBeamTrace.rho_ne_neg_id` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every q:Nat, hq:2<=q and actual h:ResetFullAut q, (rho q (0<q) h).toLinearMap is not negative LinearMap.id on the original native Int-module. Evaluation at Phi(1) would have trace -1, contradicting original_action_positive. No ambient unit classification is assumed.

**Theorem 1.11 (Every integral time power).**

Lean statement: `D5/S3/ConceptDynamics/Coding/ResetPerronBeamTrace.tau_time_zpow`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResetPerronBeamTrace.tau_time_zpow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every q:Nat, hq:2<=q, n:Int and native x, tau q hq ((rho q (0<q) (unitShift (ResetGraph q)) ^ n) x)=beta q^n*tau q hq x. The inverse equivalence has reciprocal factor because beta is positive and nonzero. Natural powers of time and its inverse prove the statement for every integer exponent.

**Theorem 1.12 (A supplied signed expression has positive scalar sign).**

Lean statement: `D5/S3/ConceptDynamics/Coding/ResetPerronBeamTrace.rho_negative_bit`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResetPerronBeamTrace.rho_negative_bit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every q:Nat, hq:2<=q, h:ResetFullAut q, a b:Fin 2 and n:Int, suppose (rho q (0<q) h).toLinearMap=(-1:Int)^a.val smul ((groupAction(resetMatrix q)(Multiplicative.ofAdd true)^b.val) * (rho q (0<q)(unitShift (ResetGraph q))^n).toLinearMap). Then a=0. Evaluate at Phi(1), use tau_sign and tau_time_zpow and beta^n>0, and compare with original_action_positive. This consumes a supplied expression and does not prove that every action admits such an expression.

The inverse-time beam construction and ordered dimension representation are classical: Boyle, Lind and Rudolph, The automorphism group of a shift of finite type, Transactions of the AMS 306 (1988), 71-114, section 6, printed pages 85-87, DOI 10.1090/S0002-9947-1988-0927684-2. The concrete coupling to the original numbered Reset graph and native presentation is derived here from the geometric suppliers. No publication novelty is claimed.

For every q>=2 and hp:0<q, put Phi=nativeIntEquiv(q,hp), beta=dbonacciPerronRoot(q), and let tau be the normalized beam trace. For every p:Int[X] and every b:QF(q), tau(Phi(fp(q,p)*b))=p.eval2(Int.cast,beta)*tau(Phi(b)). Polynomial induction proves the identity: constants use the integer module law, sums use additivity, and multiplication by forward X uses native_presentation and tau_theta. In particular the operation occurs in the integer polynomial chart; Native remains an integer module. Taking b=1 and the literal tau_one=1, quotient representatives give tau(Phi(z))=E(plus(q,z)) for every z:QF(q), for the same injective Plus evaluation E. Both identities quantify over arbitrary vectors and polynomials, with no degree bound or change of trace normalization.

The Perron assertion is restricted to q>=2, with no positive-entropy claim at q=1. It neither exhausts the q=2 rho image nor classifies the kernel or splits the full history group. Integral gluing, unit, lattice, conductor and residue questions remain separate.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetPerronBeamTrace.original_action_positive`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetPerronBeamTrace.rho_ne_neg_id`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetPerronBeamTrace.rho_negative_bit`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetPerronBeamTrace.rowWeight_transition`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetPerronBeamTrace.tau`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetPerronBeamTrace.tau_beam_atCut`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetPerronBeamTrace.tau_beam_positive`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetPerronBeamTrace.tau_one`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetPerronBeamTrace.tau_sign`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetPerronBeamTrace.tau_stage`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetPerronBeamTrace.tau_theta`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetPerronBeamTrace.tau_time_zpow`
- Dependency: [D5/S3/ConceptDynamics/Coding/ResetNativeIntegerChart](ResetNativeIntegerChart.md)
- Dependency: [D5/S3/TotalVariation/ParryResetLaw](../../TotalVariation/ParryResetLaw.md)

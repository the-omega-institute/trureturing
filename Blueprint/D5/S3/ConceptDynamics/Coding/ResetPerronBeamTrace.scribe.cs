using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class ResetPerronBeamTraceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/ResetPerronBeamTrace.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive Perron trace of original Reset beams.",
        H("Positive Perron trace of original Reset beams"),
        Blocks(
            Describe.Lean(DescribeId.Create("reset-perron-beam-tau"),
                DeclarationHandle.Create(Prefix + "tau"),
                H("The normalized native Perron trace"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural q with hq:2<=q, beta q=dbonacciPerronRoot q, p=(beta q)^(-1), and weight q i=suffixWeight q p i=sum over a<q-i.val of p^(a+1). rowWeight v=sum over (i,g):Fin q x Sign of cast(v(i,g))*weight q i. Both absolute Sign labels have equal weights. tau q hq is an Int-linear map from the original DimensionGroup(resetMatrix q) to Real. It is the actual Module.DirectLimit.lift of beta^(-(N:Int))*rowWeight at stage N, composed with the inverse of resetRowLimitEquiv, which transports both coefficients at the same stage."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("reset-perron-beam-row-weight-transition"),
                DeclarationHandle.Create(Prefix + "rowWeight_transition"),
                H("Right-row compatibility"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every q:Nat with 2<=q and every v:Fin q x Sign -> Int, rowWeight q (rowTransition (ResetGraph q) v)=beta q * rowWeight q v. This is v -> v B for the actual numbered expanded adjacency. matrix_coefficient gives reset to (0,g*tau) and legal increment to (i+1,g). The suffix recurrence and weight zero=1 prove B r=beta r. No transpose is introduced."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("reset-perron-beam-tau-stage"),
                DeclarationHandle.Create(Prefix + "tau_stage"),
                H("Every original natural stage"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every q:Nat, hq:2<=q, N:Nat and v:VertexModule Sign q, tau q hq (nativeStage q N v)=beta q^(-(N:Int))*sum over i:Fin q and g:Sign of cast((v i).coeff g)*weight q i. The native stage is the original same-stage colimit map. DirectLimit.lift_of and resetRowLimitEquiv_stage give the formula. Compatibility is beta^(-j)*beta^(j-i)=beta^(-i) for i<=j."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("reset-perron-beam-tau-beam-at-cut"),
                DeclarationHandle.Create(Prefix + "tau_beam_atCut"),
                H("Every lawful integer cut"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every q:Nat, hq:2<=q, U:Beam(ResetGraph q), m:Int and hm:AtCut(ResetGraph q) U.val m, hm.1 supplies Finite Parts and Fintype.ofFinite supplies its sum. Then tau q hq (resetBeamCoordinate q U)=beta q^(-m)*sum over P:Parts(ResetGraph q) U.val m of weight q (RayAt.endpoint (ResetGraph q) P.val).1. Parts consists of actual ray sets, with finite union and disjointness supplied by the original geometry. Distinct pasts sharing an endpoint count separately. coordinateAt_refine and endpointRow_refine use the Sigma of each earlier part and its numbered continuations. Their B^r advancement cancels the inverse-stage factor. intStage m is stage m.toNat after T^((-m).toNat); this includes negative cuts."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("reset-perron-beam-tau-beam-positive"),
                DeclarationHandle.Create(Prefix + "tau_beam_positive"),
                H("Strictness detects beam nonemptiness"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every q:Nat, hq:2<=q and actual beam U, 0<=tau q hq (resetBeamCoordinate q U), and 0<tau q hq (resetBeamCoordinate q U) if and only if U.val.Nonempty. All suffix weights are bounded below by the positive reciprocal Parry root. A point x in U determines the intrinsic part rayAt x m by saturation. Conversely each part is nonempty by RayAt.nonempty. The finite positive sum detects nonemptiness, including zero trace on the empty beam."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("reset-perron-beam-tau-theta"),
                DeclarationHandle.Create(Prefix + "tau_theta"),
                H("Forward time"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every q:Nat, hq:2<=q and x in the original native DimensionGroup, tau q hq (resetTheta q x)=beta q*tau q hq x. rho_unitShift identifies forward resetTheta with the actual unit left shift. Forward time has factor beta while stage N has factor beta^(-N)."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("reset-perron-beam-tau-sign"),
                DeclarationHandle.Create(Prefix + "tau_sign"),
                H("Actual absolute Sign"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every q:Nat, hq:2<=q and native x, tau q hq (groupAction(resetMatrix q)(Multiplicative.ofAdd true) x)=tau q hq x. Reindexing the actual two absolute Sign coefficients proves this. No arbitrary history automorphism is assumed Sign-equivariant."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("reset-perron-beam-tau-one"),
                DeclarationHandle.Create(Prefix + "tau_one"),
                H("The literal stage-zero basis ray"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every q:Nat with hq:2<=q, tau q hq (nativeIntEquiv q (0<q) 1)=1. generatorRay is resetRayBeam of resetBasisHistory at (suffix zero,absolute identity Sign) and cut zero. native_presentation identifies Phi(1) with nativeStage zero e0. e0 is exactly this literal vertex. vertexHistory_endpoint and resetBeamCoordinate_ray identify its ray coordinate. The zero-suffix weight is one. The inverse native chart is never asserted coordinatewise positive."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("reset-perron-beam-original-action-positive"),
                DeclarationHandle.Create(Prefix + "original_action_positive"),
                H("Every original full history image"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every q:Nat, hq:2<=q and h:ResetFullAut q, 0<tau q hq (rho q (0<q) h (nativeIntEquiv q (0<q) 1)). h ranges over all original history homeomorphisms commuting with unit shift. fullAut_has_two_windows derives both finite windows; image_ray_atCut makes the literal image of generatorRay finite at cut d. alpha=resetBasisHistory belongs to its own ray, so h(alpha) explicitly witnesses nonemptiness of its Set.image. rho_beam_image identifies that beam coordinate with the native action. The intrinsic finite Parts formula and beam strictness give positivity without a cone premise, normal form, marker hypothesis or full-shift surrogate."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("reset-perron-beam-rho-ne-neg-id"),
                DeclarationHandle.Create(Prefix + "rho_ne_neg_id"),
                H("Negative scalar identity is excluded"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every q:Nat, hq:2<=q and actual h:ResetFullAut q, (rho q (0<q) h).toLinearMap is not negative LinearMap.id on the original native Int-module. Evaluation at Phi(1) would have trace -1, contradicting original_action_positive. No ambient unit classification is assumed."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("reset-perron-beam-tau-time-zpow"),
                DeclarationHandle.Create(Prefix + "tau_time_zpow"),
                H("Every integral time power"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every q:Nat, hq:2<=q, n:Int and native x, tau q hq ((rho q (0<q) (unitShift (ResetGraph q)) ^ n) x)=beta q^n*tau q hq x. The inverse equivalence has reciprocal factor because beta is positive and nonzero. Natural powers of time and its inverse prove the statement for every integer exponent."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("reset-perron-beam-rho-negative-bit"),
                DeclarationHandle.Create(Prefix + "rho_negative_bit"),
                H("A supplied signed expression has positive scalar sign"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every q:Nat, hq:2<=q, h:ResetFullAut q, a b:Fin 2 and n:Int, suppose (rho q (0<q) h).toLinearMap=(-1:Int)^a.val smul ((groupAction(resetMatrix q)(Multiplicative.ofAdd true)^b.val) * (rho q (0<q)(unitShift (ResetGraph q))^n).toLinearMap). Then a=0. Evaluate at Phi(1), use tau_sign and tau_time_zpow and beta^n>0, and compare with original_action_positive. This consumes a supplied expression and does not prove that every action admits such an expression."))),
                DescribeRole.Theorem),
            Paragraph(Text("The inverse-time beam construction and ordered dimension representation are classical: Boyle, Lind and Rudolph, The automorphism group of a shift of finite type, Transactions of the AMS 306 (1988), 71-114, section 6, printed pages 85-87, DOI 10.1090/S0002-9947-1988-0927684-2. The concrete coupling to the original numbered Reset graph and native presentation is derived here from the geometric suppliers. No publication novelty is claimed.")),
            Paragraph(Text("For every q>=2 and hp:0<q, put Phi=nativeIntEquiv(q,hp), "
                + "beta=dbonacciPerronRoot(q), and let tau be the normalized beam trace. "
                + "For every p:Int[X] and every b:QF(q), "
                + "tau(Phi(fp(q,p)*b))=p.eval2(Int.cast,beta)*tau(Phi(b)). "
                + "Polynomial induction proves the identity: constants use the integer "
                + "module law, sums use additivity, and multiplication by forward X uses "
                + "native_presentation and tau_theta. In particular the operation occurs in "
                + "the integer polynomial chart; Native remains an integer module. "
                + "Taking b=1 and the literal tau_one=1, quotient representatives give "
                + "tau(Phi(z))=E(plus(q,z)) for every z:QF(q), for the same injective Plus "
                + "evaluation E. Both identities quantify over arbitrary vectors and "
                + "polynomials, with no degree bound or change of trace normalization.")),
            Paragraph(Text("The Perron assertion is restricted to q>=2, with no positive-entropy claim at q=1. It neither exhausts the q=2 rho image nor classifies the kernel or splits the full history group. Integral gluing, unit, lattice, conductor and residue questions remain separate.")))));
}

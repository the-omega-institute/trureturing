using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;

internal sealed class OwnClockContractionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/PriceRecord/OwnClockContraction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual scalar own-clock: strict decrease of response minus identity, uncompiled candidate",
        H("The actual scalar own-clock: strict decrease of response minus identity, uncompiled candidate"),
        Blocks(
            Paragraph(Text("Let S be a finite nonempty set of distinct naturals p>=2, theta=sum_S log p>1. For the actual Robin cutoff write c(L)=log(1+L log L) and T(L)=sum_S max(log p,c(L)-log p), on the whole closed ray L>=theta. The literal Phi is imported unchanged from OwnClockFixedSupport. This source candidate does not assert compiler, kernel, axiom-closure, freeze, registration, independent review or official acceptance.")),
            Paragraph(Text("Since theta>1, the ray is nonempty and every L>=theta satisfies L>1 and log L>0. The derivative of c is positive. Put R(L)=sqrt(1+L log L). The active set {p: p<=R(L)} has cardinal at most floor(R(L))-1<=R(L)-1, including the 1<R<2 case. The logarithmic estimate log L<2R(L)/3 gives 36(R-1)(1+log L)<=24R^2+12R-36<=25R^2, with final square (R-6)^2, so the right derivative is globally bounded by 25/36. At an exact max tie, c is increasing on the right ray and the active branch is used.")),
            Paragraph(Text("Supplier audit: the pinned image_le_of_deriv_right_le_deriv_boundary in Analysis/Calculus/MeanValue.lean consumes response continuity, right derivatives, the left endpoint comparison, affine-boundary continuity, affine-boundary right derivatives, and the derivative bound, in that order. HasDerivWithinAt.congr_of_mem handles the active branch on Ici L; congr_of_eventuallyEq handles the inactive branch with target=source eventual equality and equality at L. HasDerivWithinAt.fun_sum combines exactly the finite support. Nat.card_Ico is used before converting the cardinal inequality to reals. The upper IVT endpoint uses log(r^2)<=r^2-1 and an explicit algebraic bound at r=theta+4 card S; this 4 is an endpoint choice, not a support hypothesis. These are source-level API checks at the stated pin; native acceptance remains pending.")),
            Describe.Lean(DescribeId.Create("actual-ownclock-ownclockcontraction-theta-le-clock"),
                DeclarationHandle.Create(Prefix + "theta_le_clock_of_naturalSupport"), H("The literal clock dominates theta"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every admissible original vector, each coordinate is at least one and every log p is positive, hence theta S<=clock S x. Only naturalSupport is required. This helper supplies the valid clock ray for attainment and KKT."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-ownclock-ownclockcontraction-ray-bounds"),
                DeclarationHandle.Create(Prefix + "ray_bounds"), H("The valid clock domain"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The theta>1 assumption pays nonemptiness and gives L>1 and log L>0 for every point of the ray. This helper is consumed by the actual derivative, continuity and KKT arguments."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-ownclock-ownclockcontraction-response-selfmap"),
                DeclarationHandle.Create(Prefix + "response_selfmap"), H("Invariance of the full closed ray"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every max term is at least log p, so theta<=T(L). This fact needs no smoothness or primality and supplies the ray endpoint inequality."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-ownclock-ownclockcontraction-response-strict-anti"),
                DeclarationHandle.Create(Prefix + "response_strictAntiOn"), H("Strict decrease of T(L)-L on each compact interval, with all active-set ties retained"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("On every compact interval [u,v] with 1<u<v, the maximum of E supplies a slope bound q<1 and the right-derivative fence gives responseClock(v)-v < responseClock(u)-u. The max inequality at ties is replaced by the increasing-right-branch derivative, so the proof does not differentiate through a kink."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-ownclock-ownclockcontraction-response-global-lipschitz"),
                DeclarationHandle.Create(Prefix + "response_global_lipschitz"), H("Global 25/36 response Lipschitz estimate"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every naturalSupport S and every pair of points on the theta ray, the literal max response satisfies |T(t)-T(s)| <= (25/36)|t-s|. The proof uses the six-argument right-derivative fence with ties counted in the active branch and the scalar radius inequality above. This bound is consumed by the finite residual certificate."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-ownclock-ownclockcontraction-exists-unique-clock"),
                DeclarationHandle.Create(Prefix + "exists_unique_clock"), H("The scalar clock is constructed"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("There exists exactly one real Lstar>=theta satisfying T(Lstar)=Lstar. The proof uses the active-count bound, right derivatives on the closed ray at ties, the compact envelope E<1, IVT, and strict decrease of T(L)-L. OwnClockUniqueMinimum consumes this result."))), DescribeRole.Theorem))));
}

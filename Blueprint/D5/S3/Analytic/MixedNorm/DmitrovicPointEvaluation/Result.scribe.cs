using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.MixedNorm.DmitrovicPointEvaluation;

internal sealed class ResultDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/MixedNorm/DmitrovicPointEvaluation/Result.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/AnalyticClosure/dmitrovic2024norm");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The constant-one point evaluation estimate fails for every finite positive p, every larger q including infinity, and every positive alpha.",
        H("Refutation of the mixed-norm point evaluation conjecture"),
        Blocks(
            Describe.Lean(DescribeId.Create("dm-result-fails-off-contractive-range"),
                DeclarationHandle.Create(Prefix + "fails_off_contractive_range"),
                H("Failure for all exponents above the contractive range"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every positive real p, every positive alpha, and every extended nonnegative q strictly larger than p, there is a function holomorphic on the open unit disc with finite mixed norm and an interior point where its norm is strictly smaller than the normalized evaluation. The normalization multiplies the modulus by (1 minus the squared modulus of the point) raised to alpha plus one over p. The finite-q case uses the strict radial gap with a equal to the square root of its positive parameter; the infinite-q case uses the unit weighted supremum and strict evaluation excess. Both constructions use principal-branch powers of 1 plus a times the variable."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("dm-result-refutation"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Dmitrovic's conjecture is false"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The universal constant-one point evaluation claim is false. The general failure theorem at p equal to one, q equal to two, and alpha equal to one produces a holomorphic function of finite mixed norm and an interior point contradicting the claim. This refutes the conjecture on p. 705 of the cited article. It does not determine the optimal larger constant in the failing parameter range."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("dmitrovic-2024-mixed-norm-point-evaluation-refutation"),
                    ResolutionKind.Refuted))
        ), []));
}

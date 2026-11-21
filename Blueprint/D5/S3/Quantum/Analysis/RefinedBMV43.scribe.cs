using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis;

internal sealed class RefinedBMV43Document : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/HilbertOperators/hagele2026refinedbmv");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The refined BMV lower bound for four and three factors",
        H("The refined BMV lower bound for four and three factors"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("refinedbmv43-product"),
                DeclarationHandle.Create("D5/S3/Quantum/Analysis/RefinedBMV43.E43_all"),
                H("The trace-power bound in every finite dimension"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The trace comparison uses the positive spectral power of the first factor. Diagonalizing its cube root turns the trace defect into a sum of centered quadratic forms, each nonnegative by the Schur product theorem."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("refinedbmv43-exponential"),
                DeclarationHandle.Create("D5/S3/Quantum/Analysis/RefinedBMV43.L43_all"),
                H("The exponential lower bound in every finite dimension"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For any finite complex Hermitian pair, the 35-word mean dominates the exponential trace. The dyadic trace-power comparison applies after scaling the first Hermitian factor by four thirds."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("hagele-2026-refined-bmv-43-all-dimensions"),
                    ResolutionKind.Proved)))));
}

using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis;

internal sealed class RefinedBMV67Document : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Analysis/RefinedBMV67.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HilbertOperators/hagele2026refinedbmv");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hägele's refined BMV lower bounds at (6,4) and (7,4)",
        H("Hägele's refined BMV lower bounds at (6,4) and (7,4)"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("refined-bmv-64-product"),
                DeclarationHandle.Create(Module + "product_bound64"),
                H("Product comparison at (6,4)"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For finite complex positive semidefinite A and B, the mean trace of the 210 words " +
                    "dominates the trace of (A^(3/2) B)^4. The proof compares the mean with the balanced " +
                    "integer word through three rational Gram matrices. The third block places B on " +
                    "both sides of each pair of half words."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("hagele-2026-refined-bmv-64-all-dimensions"),
                    ResolutionKind.Proved)),
            Describe.Lean(
                DescribeId.Create("refined-bmv-74-product"),
                DeclarationHandle.Create(Module + "product_bound74"),
                H("Product comparison at (7,4)"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For finite complex positive semidefinite A and Hermitian B, the mean trace of the " +
                    "330 words dominates the trace of (A^(7/4) B)^4. A rational Gram certificate weighted " +
                    "by A gives the integer comparison. Fourth-root powers and three Frobenius estimates " +
                    "give the fractional-power comparison for singular and invertible A."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("hagele-2026-refined-bmv-74-all-dimensions"),
                    ResolutionKind.Proved)),
            Describe.Lean(
                DescribeId.Create("refined-bmv-64-exponential"),
                DeclarationHandle.Create(Module + "exponential_bound64"),
                H("Exponential comparison at (6,4)"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For Hermitian H and K, the mean for exp H and exp K is at least the trace of " +
                    "exp(6H + 4K). The dyadic Lie–Trotter limit gives the comparison."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("refined-bmv-74-exponential"),
                DeclarationHandle.Create(Module + "exponential_bound74"),
                H("Exponential comparison at (7,4)"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For Hermitian H and K, the mean for exp H and exp K is at least the trace of " +
                    "exp(7H + 4K). The dyadic Lie–Trotter limit gives the comparison."))),
                DescribeRole.Theorem))));
}

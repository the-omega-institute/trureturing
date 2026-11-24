using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis;

internal sealed class RefinedBMV84Document : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Analysis/RefinedBMV84.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HilbertOperators/hagele2026refinedbmv");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The refined BMV comparisons with eight copies of the first factor",
        H("The refined BMV comparisons with eight copies of the first factor"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("refined-bmv-84-product"),
                DeclarationHandle.Create(Module + "product_bound84"),
                H("Product trace comparison"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For any finite complex positive semidefinite A and B, the mean of the 495 " +
                    "word traces with eight copies of A and four of B is at least the trace of (A^2 B)^4. " +
                    "Three rational Gram blocks compare the mean with the fourth trace of the Hermitian part " +
                    "of A^(3/2) B A^(1/2). The quartic trace comparison then bounds the balanced product. " +
                    "The proof treats singular A directly."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("hagele-2026-refined-bmv-84-all-dimensions"),
                    ResolutionKind.Proved)),
            Describe.Lean(
                DescribeId.Create("refined-bmv-84-exponential"),
                DeclarationHandle.Create(Module + "exponential_bound84"),
                H("Exponential trace comparison"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For Hermitian H and K, the same mean for exp H and exp K is at least the trace of " +
                    "exp(8H + 4K). The fourth trace-power comparison follows from the dyadic Lie–Trotter " +
                    "argument of Hägele's Lemma 2."))),
                DescribeRole.Theorem))));
}

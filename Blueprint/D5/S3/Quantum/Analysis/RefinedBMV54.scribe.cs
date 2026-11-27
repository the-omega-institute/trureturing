using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis;

internal sealed class RefinedBMV54Document : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Analysis/RefinedBMV54.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HilbertOperators/hagele2026refinedbmv");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The refined BMV comparisons with five copies of the first factor",
        H("The refined BMV comparisons with five copies of the first factor"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("refined-bmv-54-product"),
                DeclarationHandle.Create(Module + "product_bound54"),
                H("Product trace comparison"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For any finite complex positive semidefinite A and Hermitian B, the mean of the 126 " +
                    "word traces with five copies of A and four of B is at least the trace of (A^(5/4) B)^4. " +
                    "The weighted sum of four Frobenius squares compares the mean with the trace of A(AB)^4. " +
                    "Three further commutator and adjoint squares give the fractional-power comparison. " +
                    "The proof treats singular A directly."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("hagele-2026-refined-bmv-54-all-dimensions"),
                    ResolutionKind.Proved)),
            Describe.Lean(
                DescribeId.Create("refined-bmv-54-exponential"),
                DeclarationHandle.Create(Module + "exponential_bound54"),
                H("Exponential trace comparison"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For Hermitian H and K, the same mean for exp H and exp K is at least the trace of " +
                    "exp(5H + 4K). The fourth trace-power comparison follows from the dyadic Lie–Trotter " +
                    "argument of Hägele's Lemma 2."))),
                DescribeRole.Theorem))));
}

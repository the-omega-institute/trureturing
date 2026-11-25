using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.RefinedBMV;

internal sealed class RefinedBMVTenFourDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Analysis/RefinedBMV/TenFour.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HilbertOperators/hagele2026refinedbmv");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The refined BMV comparisons with ten copies of the first factor",
        H("The refined BMV comparisons with ten copies of the first factor"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("refined-bmv-104-product"),
                DeclarationHandle.Create(Module + "product_bound104"),
                H("Product trace comparison"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "In every finite complex dimension, for positive semidefinite A and B, " +
                    "the mean of the 1001 word traces with ten copies of A and four of B is at least " +
                    "the trace of (A^(5/2) B)^4. Three rational positive semidefinite Gram blocks of sizes 21, 15 and 6, " +
                    "with weights I/I, A/A and B/B, compare the mean with the word trace with gaps " +
                    "(3,2,3,2). Trace Cauchy–Schwarz gives the fractional-power bound. " +
                    "The argument allows singular A and B."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("hagele-2026-refined-bmv-104-all-dimensions"),
                    ResolutionKind.Proved)),
            Describe.Lean(
                DescribeId.Create("refined-bmv-104-exponential"),
                DeclarationHandle.Create(Module + "exponential_bound104"),
                H("Exponential trace comparison"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For Hermitian H and K, the same mean for exp H and exp K is at least the trace of " +
                    "exp(10H + 4K). The fourth trace-power comparison follows from the dyadic Lie–Trotter " +
                    "argument of Hägele's Lemma 2."))),
                DescribeRole.Theorem))));
}

using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.RefinedBMV;

internal sealed class RefinedBMVNineFourDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Analysis/RefinedBMV/NineFour.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HilbertOperators/hagele2026refinedbmv");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The refined BMV comparisons with nine copies of the first factor",
        H("The refined BMV comparisons with nine copies of the first factor"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("refined-bmv-94-product"),
                DeclarationHandle.Create(Module + "product_bound94"),
                H("Product trace comparison"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "In every finite complex dimension, for positive semidefinite A and Hermitian B, " +
                    "the mean of the 715 word traces with nine copies of A and four of B is at least " +
                    "the trace of (A^(9/4) B)^4. One rational positive semidefinite Gram matrix on " +
                    "15 half-words, weighted by A, compares the mean with the word trace with gaps " +
                    "(3,2,2,2). Two trace Cauchy–Schwarz inequalities then give the balanced bound. " +
                    "The argument allows singular A."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("hagele-2026-refined-bmv-94-all-dimensions"),
                    ResolutionKind.Proved)),
            Describe.Lean(
                DescribeId.Create("refined-bmv-94-exponential"),
                DeclarationHandle.Create(Module + "exponential_bound94"),
                H("Exponential trace comparison"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For Hermitian H and K, the same mean for exp H and exp K is at least the trace of " +
                    "exp(9H + 4K). The fourth trace-power comparison follows from the dyadic Lie–Trotter " +
                    "argument of Hägele's Lemma 2."))),
                DescribeRole.Theorem))));
}

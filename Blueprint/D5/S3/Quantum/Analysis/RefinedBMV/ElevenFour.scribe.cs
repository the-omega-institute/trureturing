using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.RefinedBMV;

internal sealed class RefinedBMVElevenFourDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Analysis/RefinedBMV/ElevenFour.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HilbertOperators/hagele2026refinedbmv");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The refined BMV lower bound at (11,4)",
        H("The refined BMV lower bound at (11,4)"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("refined-bmv-114-product"),
                DeclarationHandle.Create(Module + "product_bound114"),
                H("Product trace comparison"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For positive semidefinite A and Hermitian B in any finite complex dimension, " +
                    "the mean of the real traces of the 1365 words with eleven copies of A and four of B " +
                    "dominates the real trace of (A^(11/4) B)^4. One rational Gram matrix weighted by A " +
                    "compares the word mean with the cyclic word with gaps (3,3,2,3). " +
                    "Two trace inequalities give the fractional-power comparison."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("hagele-2026-refined-bmv-114-all-dimensions"),
                    ResolutionKind.Proved)),
            Describe.Lean(
                DescribeId.Create("refined-bmv-114-exponential"),
                DeclarationHandle.Create(Module + "exponential_bound114"),
                H("Exponential trace comparison"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For Hermitian H and K, the corresponding mean for exp H and exp K " +
                    "dominates the trace of exp(11H + 4K), by the dyadic trace-power comparison."))),
                DescribeRole.Theorem))));
}

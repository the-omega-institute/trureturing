using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.RefinedBMV;

internal sealed class RefinedBMVTwelveFourDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Analysis/RefinedBMV/TwelveFour.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HilbertOperators/hagele2026refinedbmv");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The refined BMV lower bound at (12,4)",
        H("The refined BMV lower bound at (12,4)"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("refined-bmv-124-product"),
                DeclarationHandle.Create(Module + "product_bound124"),
                H("Product trace comparison"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For positive semidefinite A and Hermitian B in any finite complex dimension, " +
                    "the mean real trace of the 1820 ordered words with twelve copies of A and four of B " +
                    "dominates the real trace of (A^3 B)^4. Two rational Gram matrices weighted by " +
                    "the identity and A compare the word mean with the fourth trace of the Hermitian " +
                    "part of A B A^2. The Hermitian-part comparison includes singular A."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("hagele-2026-refined-bmv-124-all-dimensions"),
                    ResolutionKind.Proved)),
            Describe.Lean(
                DescribeId.Create("refined-bmv-124-exponential"),
                DeclarationHandle.Create(Module + "exponential_bound124"),
                H("Exponential trace comparison"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For Hermitian H and K, the word mean for exp H and exp K " +
                    "dominates the trace of exp(12H + 4K) by the dyadic trace-power comparison."))),
                DescribeRole.Theorem))));
}

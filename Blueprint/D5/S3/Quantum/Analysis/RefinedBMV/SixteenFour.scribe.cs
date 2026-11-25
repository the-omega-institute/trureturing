using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.RefinedBMV;

internal sealed class RefinedBMVSixteenFourDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Analysis/RefinedBMV/SixteenFour.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HilbertOperators/hagele2026refinedbmv");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The refined BMV lower bound at (16,4)",
        H("The refined BMV lower bound at (16,4)"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("refined-bmv-164-product"),
                DeclarationHandle.Create(Module + "product_bound164"),
                H("Product trace comparison"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For positive semidefinite A and Hermitian B in any finite complex dimension, " +
                    "the mean real trace of the 4845 ordered words with sixteen copies of A and four of B " +
                    "dominates the real trace of (A^4 B)^4. Two rational Gram matrices weighted by " +
                    "the identity and A compare the word mean with the fourth trace of the Hermitian " +
                    "part obtained by centering the exponents of the two phase factors. The comparison includes singular A."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("hagele-2026-refined-bmv-164-all-dimensions"),
                    ResolutionKind.Proved)),
            Describe.Lean(
                DescribeId.Create("refined-bmv-164-exponential"),
                DeclarationHandle.Create(Module + "exponential_bound164"),
                H("Exponential trace comparison"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For Hermitian H and K, the word mean for exp H and exp K " +
                    "dominates the trace of exp(16H + 4K) by the dyadic trace-power comparison."))),
                DescribeRole.Theorem))));
}

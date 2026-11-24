using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis;

internal sealed class RefinedBMV44Document : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Analysis/RefinedBMV44.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HilbertOperators/hagele2026refinedbmv");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The refined BMV comparisons with four copies of each factor",
        H("The refined BMV comparisons with four copies of each factor"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("refined-bmv-44-product"),
                DeclarationHandle.Create(Module + "product_bound44"),
                H("Product trace comparison"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For positive semidefinite complex matrices A and B, the mean trace of the seventy words " +
                    "with four copies of each factor is at least the trace of (AB)^4. The dimensions and ranks " +
                    "are arbitrary. Combining the cyclic word classes with the fourth moment of the Hermitian " +
                    "part of AB gives an exact decomposition into nonnegative trace differences. The terms " +
                    "come from weighted commutator squares, Frobenius squares, and unitary triangularization. " +
                    "This proves the product comparison E(4,4) of Hägele's Section 1, whose three-dimensional " +
                    "case is named in Section 7."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("hagele-2026-refined-bmv-44-all-dimensions"),
                    ResolutionKind.Proved)),
            Describe.Lean(
                DescribeId.Create("refined-bmv-44-exponential"),
                DeclarationHandle.Create(Module + "exponential_bound44"),
                H("Exponential trace comparison"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For Hermitian H and K, the same mean for exp H and exp K is at least the trace of " +
                    "exp(4H + 4K). The fourth trace-power comparison follows from the dyadic Lie–Trotter " +
                    "argument of Hägele's Lemma 2."))),
                DescribeRole.Theorem))));
}

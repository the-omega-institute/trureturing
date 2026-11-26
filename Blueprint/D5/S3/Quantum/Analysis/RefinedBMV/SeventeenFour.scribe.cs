using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.RefinedBMV;

internal sealed class RefinedBMVSeventeenFourDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Analysis/RefinedBMV/SeventeenFour.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HilbertOperators/hagele2026refinedbmv");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The refined BMV comparisons with seventeen copies of the first factor",
        H("The refined BMV comparisons with seventeen copies of the first factor"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("refined-bmv-174-product"),
                DeclarationHandle.Create(Module + "product_bound174"),
                H("Product trace comparison"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "In every finite complex dimension, for positive semidefinite A and Hermitian B, " +
                    "the mean of the real parts of the 5,985 ordered word traces with seventeen copies " +
                    "of A and four of B is at least the real part of the trace of (A^(17/4) B)^4. " +
                    "A rational positive semidefinite Gram matrix on 45 half-words, weighted by A, " +
                    "compares the mean with the real part of the trace of the word with cyclic gaps " +
                    "(5,4,4,4). Two trace Cauchy–Schwarz inequalities bound the fractional-power " +
                    "trace by that word trace. The argument allows singular A."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("refined-bmv-174-exponential"),
                DeclarationHandle.Create(Module + "exponential_bound174"),
                H("Exponential trace comparison"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For Hermitian H and K, the same mean for exp H and exp K is at least the real " +
                    "part of the trace of exp(17H + 4K). The fourth trace-power comparison uses " +
                    "the dyadic Lie–Trotter argument of Hägele's Lemma 2."))),
                DescribeRole.Theorem))));
}

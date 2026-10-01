using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class ArcherCyclicPadovanArithmeticDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/ArcherCyclicPadovanArithmetic.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/archer2024pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Three initial values and a cubic recurrence determine the Padovan subsequence at multiples of three.",
        H("Uniqueness of the Padovan Subsequence"),
        Blocks(Describe.Lean(DescribeId.Create("archer-cyclic-padovan-recurrence-unique"),
            DeclarationHandle.Create(Prefix + "triple_recurrence_unique"),
            H("Uniqueness from three values"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text("A natural-number sequence agreeing with the Padovan numbers at indices three, six, and nine and satisfying b(n+3) + 2b(n+1) = 3b(n+2) + b(n) for positive n equals the Padovan number at index three times n for every positive n."))),
            DescribeRole.Theorem)),
        []));
}

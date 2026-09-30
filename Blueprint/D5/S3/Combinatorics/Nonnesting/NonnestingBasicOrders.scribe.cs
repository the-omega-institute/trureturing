using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Nonnesting;

internal sealed class NonnestingBasicOrdersDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Nonnesting/NonnestingBasicOrders.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/elizalde2024pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The two occurrences of each letter govern nonnesting.",
        H("Occurrence Orders in Doubled Words"),
        Blocks(
            Node("nonnesting-nonnestingbasicorders-secondpos", "Position of the second occurrence", "secondPos",
                "Starting just after the first occurrence, this index searches for the next copy of the letter and adds the starting offset.", DescribeRole.Definition),
            Node("nonnesting-nonnestingbasicorders-count-two-decomposition", "Decomposition around two copies", "count_two_decomposition",
                "A letter occurring exactly twice separates a word into three pieces containing no further copy of that letter.", DescribeRole.Theorem),
            Node("nonnesting-nonnestingbasicorders-doubled-count", "Multiplicity in a doubled permutation", "doubled_count",
                "Every letter in the doubled support occurs exactly twice.", DescribeRole.Theorem),
            Node("nonnesting-nonnestingbasicorders-nesting-of-reversal", "Reversed orders create nesting", "nesting_of_reversal",
                "If the first occurrences of two distinct letters have one order and their second occurrences have the reverse order, the word contains 1221 or 2112.", DescribeRole.Theorem),
            Node("nonnesting-nonnestingbasicorders-nonnesting-iff-equal-orders", "Nonnesting as matching occurrence orders", "nonnesting_iff_equal_orders",
                "For a word with exactly two copies of every letter, avoiding 1221 and 2112 is equivalent to first-occurrence order implying the same second-occurrence order.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}

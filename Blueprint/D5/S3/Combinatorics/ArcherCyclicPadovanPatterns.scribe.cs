using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class ArcherCyclicPadovanPatternsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/ArcherCyclicPadovanPatterns.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/archer2024pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Order-preserving relabeling and increasing blocks control occurrences of 4132.",
        H("Pattern Occurrences in Padovan Words"),
        Blocks(
            Node("archer-cyclic-padovan-map-pattern", "Increasing relabeling", "contains_map_iff",
                "Applying a strictly increasing map to every letter of a word preserves the occurrence or avoidance of any fixed classical pattern.", DescribeRole.Theorem),
            Node("archer-cyclic-padovan-high-one", "A high letter followed by one", "contains_4132_high_one_iff",
                "For a word beginning with a value above one and then one, a 4132 occurrence either lies in the remaining suffix or comes from a descending pair there whose larger entry is below the initial value.", DescribeRole.Theorem),
            Node("archer-cyclic-padovan-middle-pattern", "Increasing middle block", "contains_4132_increasing_middle_iff",
                "Prepending an increasing block does not change 4132 occurrence when each later letter is one, two, or exceeds every letter of that block.", DescribeRole.Theorem),
            Node("archer-cyclic-padovan-middle-descent", "Descent in the tail", "descent_tail_in_q",
                "Under the stated increasing-middle and size conditions, a 213 triple in the middle block followed by one and a tail has its descending pair entirely in the tail.", DescribeRole.Theorem),
            Node("archer-cyclic-padovan-high-middle", "Remove the middle block", "contains_4132_high_middle_iff",
                "With an initial high letter, an increasing middle block, one, and a suitably separated suffix, removing the middle block preserves whether the word contains 4132.", DescribeRole.Theorem),
            Node("archer-cyclic-padovan-raise-high", "Raise high letters", "raiseHigh",
                "The map fixes zero and one and raises every letter at least two by m minus one.", DescribeRole.Definition)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}

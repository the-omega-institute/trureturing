using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.VincularStack;

internal sealed class VincularStackPatternsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/VincularStack/VincularStackPatterns.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Words/zhao2024vincular");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Prefix records and restriction by value relate input patterns to the stack output.",
        H("Prefix Records and Pattern Obstructions"),
        Blocks(
            Node("vincularstack-vincularstackpatterns-no-pop-iff-records", "Prefixes with no popped entries", "no_pop_iff_records",
                "Processing a word from an empty stack pops no entries before the final drain precisely when, for every adjacent descent, its lower entry is at most every entry strictly before the upper entry of that descent.", DescribeRole.Theorem),
            Node("vincularstack-vincularstackpatterns-separating-gap", "Characterizing a separating output gap", "separating_gap",
                "For a split into a front and a suffix, the corresponding output gap is separating precisely when the front is empty, or the front has no pops before its final drain and the following suffix condition holds. An empty suffix always satisfies the condition. For a suffix starting with e, either the snapshot stack of the front contains an entry less than e, or every suffix entry is less than every front entry.", DescribeRole.Theorem),
            Node("vincularstack-vincularstackpatterns-restrict-sc", "Restriction to bounded values", "restrict_sc",
                "For a word of distinct entries and any threshold t, applying SC after deleting all entries greater than t gives the same word as deleting all entries greater than t from the SC output.", DescribeRole.Theorem),
            Node("vincularstack-vincularstackpatterns-contains1324", "The classical pattern 1324", "Contains1324",
                "A word contains 1324 when four entries at strictly increasing positions have the first entry less than the third, the third less than the second, and the second less than the fourth.", DescribeRole.Definition),
            Node("vincularstack-vincularstackpatterns-contains1324-not-sortable", "The obstruction from 1324", "contains1324_not_sortable",
                "If a word of distinct entries contains the classical pattern 1324, its image under SC contains the classical pattern 231.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}

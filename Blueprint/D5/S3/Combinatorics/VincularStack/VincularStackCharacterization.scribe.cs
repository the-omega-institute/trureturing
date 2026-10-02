using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.VincularStack;

internal sealed class VincularStackCharacterizationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/VincularStack/VincularStackCharacterization.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Words/zhao2024vincular");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The sorting class is characterized by avoidance of 1324 and a shaded 2413 pattern.",
        H("A Pattern Characterization of the Sorting Class"),
        Blocks(
            Node("vincularstack-vincularstackcharacterization-containsmesh2413", "The shaded 2413 pattern", "ContainsMesh2413",
                "A word contains the shaded 2413 pattern when positions a, b, c, d are strictly increasing, their values satisfy w(c) less than w(a) less than w(d) less than w(b), every entry before b is at least w(a), and no entry strictly between b and c has value strictly between w(a) and w(b).", DescribeRole.Definition),
            Node("vincularstack-vincularstackcharacterization-maximum-insertion-obstruction", "An obstruction created by a maximum", "maximum_insertion_obstruction",
                "Let a word have distinct entries and an SC output avoiding 231. If inserting an entry greater than every original entry makes its SC output contain 231, the new word contains either 1324 or the shaded 2413 pattern.", DescribeRole.Theorem),
            Node("vincularstack-vincularstackcharacterization-non-sortable-has-pattern", "Patterns in every nonsortable word", "non_sortable_has_pattern",
                "If a word of distinct entries has an SC output containing 231, the input word contains either the classical pattern 1324 or the shaded 2413 pattern.", DescribeRole.Theorem),
            Node("vincularstack-vincularstackcharacterization-sortable-iff-avoids1324-and-mesh", "The avoidance characterization", "sortable_iff_avoids1324_and_mesh",
                "For every word of distinct entries, its image under SC avoids 231 if and only if the word avoids both the classical pattern 1324 and the shaded 2413 pattern.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}

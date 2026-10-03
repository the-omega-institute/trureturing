using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.MeshPattern;

internal sealed class MeshPatternS21SwitchDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/MeshPattern/MeshPatternS21Switch.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/lvzhang2025mesh");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Transposing the labels on an active boundary produces a permutation with the same active rectangles and the same points outside the active region.",
        H("Transposition Inside the Active Region"),
        Blocks(
            Node("mesh-pattern-s21switch-seven-active-switch", "The active-region switch", "seven_active_switch",
                "Let p be a permutation of one through n. Its active outline has n downward steps and a cell list without repetitions covering exactly the active region. Peeling its labeled boundary returns the entries of p on those cells and an axis path with only empty labels. Transposing every boundary label yields a boundary whose peeling returns the entries of another permutation q of one through n and an axis path with only empty labels. The permutations agree outside the active region. For every m from three through n, their rectangles of width n minus m plus three and height m have equal point counts, agree on whether they contain a point of value m, and agree on whether their last column contains a point. They have the same active heights and active region.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}

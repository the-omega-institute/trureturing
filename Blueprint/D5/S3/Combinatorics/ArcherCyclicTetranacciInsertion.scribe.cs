using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class ArcherCyclicTetranacciInsertionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/ArcherCyclicTetranacciInsertion.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/archer2024pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Inserting a low arc preserves circular avoidance of 1324.",
        H("Low-Arc Insertion"),
        Blocks(
            Node("archer-cyclic-insert-word", "Insert a low arc", "insertWord",
                "Insertion shifts every letter of the old word upward by k, places one first, and appends the increasing letters from two through k.", DescribeRole.Definition),
            Node("archer-cyclic-insert-circular", "Circular avoidance under insertion", "circular_1324_insert_iff",
                "For a rooted permutation word and positive k, the inserted word contains 1324 in some rotation exactly when the original word does.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}

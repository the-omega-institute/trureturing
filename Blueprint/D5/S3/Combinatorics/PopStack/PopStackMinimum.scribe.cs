using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PopStack;

internal sealed class PopStackMinimumDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PopStack/PopStackMinimum.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/cioni2025sorting");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For a word with positive entries, add one to every value and insert one into any existing gap of zero-based index at most two. The resulting word belongs to C if and only if the original word belongs to C.",
        H("Inserting a minimum in an early gap"),
        Blocks(
            Node("pop-stack-popstackminimum-minimum-insertion-inc", "Inserting a minimum in an early gap", "minimum_insertion_inC",
                "For a word with positive entries, add one to every value and insert one into any existing gap of zero-based index at most two. The resulting word belongs to C if and only if the original word belongs to C.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}

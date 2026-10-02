using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PopStack;

internal sealed class PopStackLeftDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PopStack/PopStackLeft.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/cioni2025sorting");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Let p have distinct positive entries and minimum one in its second position. Prepend two and increase every original entry other than one by one. The resulting word belongs to C if and only if p belongs to C.",
        H("Prepending a new second-smallest entry"),
        Blocks(
            Node("pop-stack-popstackleft-prepend-two-inc", "Prepending a new second-smallest entry", "prepend_two_inC",
                "Let p have distinct positive entries and minimum one in its second position. Prepend two and increase every original entry other than one by one. The resulting word belongs to C if and only if p belongs to C.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}

using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PopStack;

internal sealed class PopStackM3DisjointDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PopStack/PopStackM3Disjoint.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/cioni2025sorting");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The word deflateFirst(p) starts with the second entry of p and then contains the entries after its first two positions, each decreased by one precisely when it exceeds that second entry. An absent second entry is read as zero.",
        H("Contracting the first two entries"),
        Blocks(
            Node("pop-stack-popstackm3disjoint-deflatefirst", "Contracting the first two entries", "deflateFirst",
                "The word deflateFirst(p) starts with the second entry of p and then contains the entries after its first two positions, each decreased by one precisely when it exceeds that second entry. An absent second entry is read as zero.", DescribeRole.Definition)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}

using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.MinimalForts;

internal sealed class ConeCountDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/MinimalForts/ConeCount.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/becker2024minimalforts");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact exhaustive count after adjoining a universal root.", H("Exact exhaustive count after adjoining a universal root"),
        Blocks(
            Node("cone-minimalfort-count", "Both actual minimal-fort classes", "cone_minimalFort_count", "For every finite decidable simple graph G with no isolated vertices, the full number of actual inclusion-minimal nonempty forts of its cone equals the full minimal-fort count of G plus the full rooted choice count of G. Root-free and root-containing subsets are disjoint and exhaustive; both inverse maps recover actual subsets. No formula for either count is a hypothesis.", DescribeRole.Theorem)), []));

    private static DocumentBlock Node(string id, string title, string declaration,
        string prose, DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}

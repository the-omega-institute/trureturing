using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.MinimalForts;

internal sealed class CompleteRootedDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/MinimalForts/CompleteRooted.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/becker2024minimalforts");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Root-containing choices of a complete block.", H("Root-containing choices of a complete block"),
        Blocks(
            Node("complete-rooted-iff", "All rooted choices are singletons", "complete_rooted_iff", "For every finite decidable vertex type with at least two vertices, and every subset S, adjoining the universal root to S in the cone over the complete graph gives a minimal nonempty fort exactly when S has cardinality one. The empty subset and all larger subsets are included in the equivalence.", DescribeRole.Theorem),
            Node("complete-rooted-count", "The full rooted count", "complete_rooted_count", "For every finite decidable nontrivial vertex type V, the full rooted choice family of the complete graph has cardinality equal to the cardinality of V. The singleton map is an injective and exhaustive correspondence, rather than a choice of only some minimal forts.", DescribeRole.Theorem)), []));

    private static DocumentBlock Node(string id, string title, string declaration,
        string prose, DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}

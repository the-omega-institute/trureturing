using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.MinimalForts;

internal sealed class CompleteBlockDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/MinimalForts/CompleteBlock.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Asymptotics/becker2024minimalforts");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every minimal fort of a complete graph.",
        H("Every minimal fort of a complete graph"),
        Blocks(
            Node("complete-block", "Pairs and the full binomial count", "complete_block", "For every finite nontrivial vertex type, a vertex subset is a minimal nonempty fort of the complete graph if and only if its cardinality is two. The cardinality of the entire minimal-fort family is therefore the vertex count choose two. The theorem retains arbitrary finite nontrivial carriers and proves the family equality with all two-element subsets before counting.", DescribeRole.Theorem)), []));

    private static DocumentBlock Node(string id, string title, string declaration,
        string prose, DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}

using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Domination;

internal sealed class PathMaximalIndependentCountDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Domination/PathMaximalIndependentCount.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual maximal independent subsets of finite paths", H("Actual maximal independent subsets of finite paths"), Blocks(
            Node("family", "The actual family", "family", "The family filters the powerset of 0,...,n-1 by maximal independence in Mathlib's native pathGraph n. A compiled bridge identifies this with bounded independent closed domination.", DescribeRole.Definition),
            Node("members", "Exact local membership", "mem_family", "Membership is equivalent to the original bounded labels, no adjacent selected pair, and closed domination of every path label.", DescribeRole.Theorem),
            Node("recurrence", "Invertible head and tail maps", "count_recurrence", "For every n, M(n+3)=M(n+1)+M(n). The first branch inserts label 0 and shifts the tail by two. The other inserts label 1 and shifts by three. Reading the tail reconstructs the original subset; the branches are disjoint by membership of label 0.", DescribeRole.Theorem),
            Node("initial", "All short path boundaries", "count_initial", "The empty path has one maximal independent subset, the one-vertex path has one, and the two-vertex path has two. These auxiliary paths do not introduce graph cases below the source order three.", DescribeRole.Theorem)), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
}

using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Domination;

internal sealed class PathEndpointCountDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Domination/PathEndpointCount.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Path endpoints and the original restricted family", H("Path endpoints and the original restricted family"), Blocks(
            Node("restricted", "Restricted actual family", "restrictedFamily", "Maximal independent subsets omitting at least one of the two endpoints. Complementation corresponds to a minimal vertex cover containing at least one endpoint.", DescribeRole.Definition),
            Node("caps", "Both endpoints", "both_count", "For every n, the maximal independent subsets of a path of order n+4 containing both endpoints are in bijection with unrestricted maximal independent subsets of order n. The middle restriction and endpoint insertion are actual inverses, including the empty middle at n=0.", DescribeRole.Theorem),
            Node("partition", "Exact endpoint partition", "restricted_complement", "The allowed family and the forbidden endpoint family partition all subsets at every order n+4. This is a sum of actual cardinalities, without relying on extrapolation.", DescribeRole.Theorem)), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
}

using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.EdgeLabeling;

internal sealed class CubicARGraphDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/EdgeLabeling/CubicARGraph.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every finite simple cubic graph has an AR-labeling onto the entire interval from one to its edge count.",
        H("Cubic graphs are additively rigid"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("cubic-ar-graph-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("The exact cubic graph assertion"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every finite vertex type and every simple graph of degree three at each vertex, "
                    + "there is a bijection from its edges onto the integers from one to its edge count "
                    + "such that every subset of the edges incident to any vertex has a distinct label sum. "
                    + "The assertion includes disconnected graphs and the graph with no vertices."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cubic-ar-graph-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Every cubic graph has an AR-labeling"),
                StatementSource.FromAuthor(Disp(F.Id("claim"))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For three positive distinct labels, the only possible subset-sum collision is that "
                    + "the two smaller labels sum to the largest. Four-vertex cubic graphs are complete; "
                    + "six-vertex cubic graphs are complete bipartite graphs or triangular prisms. Explicit "
                    + "labelings of these graphs transfer along graph isomorphisms. For at least twelve "
                    + "edges, fix two intersecting edges to labels one and two. The sum of the cardinalities "
                    + "of the bad vertex events is strictly less than the factorial size of the remaining "
                    + "bijection space, so one labeling has no bad vertex. The degree-sum formula excludes "
                    + "other positive orders below eight, and the empty graph has the empty edge labeling."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("manattu-lakshmanan-2025-cubic-ar-graphs"), ResolutionKind.Proved))),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/EdgeLabeling/CubicARGraphDefs")),
         DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/EdgeLabeling/CubicARGraphSmallIso")),
         DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/EdgeLabeling/CubicARGraphTransport")),
         DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/EdgeLabeling/CubicARGraphLarge"))]));
}

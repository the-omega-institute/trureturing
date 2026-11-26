using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class Q9SevenVertexBipartiteDocument : IScribeDocumentDefinition
{
    private const string Module =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SevenVertexBipartite";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A dense triangle-free graph on seven vertices",
        H("Eleven edges force a bipartition of sizes four and three"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("q9-seven-vertex-bipartition"),
                DeclarationHandle.Create(Module + ".seven_vertex_bipartition"),
                H("The neighbors of a maximum-degree vertex form the four-vertex part"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A triangle-free simple graph on seven vertices with at least eleven edges "
                        + "has complementary independent parts of sizes four and three.")),
                    Paragraph(Text(
                        "The degree sum gives a vertex with at least four neighbors. Its neighborhood "
                        + "is independent. An edge in the complement would use the two vertices there "
                        + "other than the chosen vertex. Its endpoints have disjoint neighborhoods in "
                        + "the four-vertex part, leaving at most eight crossing edges and one internal "
                        + "edge in total. With both parts independent, the product of their sizes "
                        + "must reach eleven, forcing the sizes four and three."))),
                DescribeRole.Theorem)),
        []));
}

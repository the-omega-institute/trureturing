using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class Q9SparseCocycleSupportDocument : IScribeDocumentDefinition
{
    private const string Module =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SparseCocycleSupport";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The possible sparse pivot graphs",
        H("The possible sparse pivot graphs"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("q9-sparse-cocycle-support"),
                DeclarationHandle.Create(Module + ".sparse_cocycle_support"),
                H("The possible sparse pivot graphs"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The degree cap and the forced triples leave a three-spoke star or a "
                        + "four-cycle. Each edge has two forced triples containing it, exhausting "
                        + "its pair cap. This gives counts of six or eight triples outside the pivot."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("q9-sparse-pivot-isolated-vertices"),
                DeclarationHandle.Create(Module + ".sparse_pivot_graph_classification"),
                H("Triples through the isolated vertices"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "In the four-edge case, the graph is a cycle on four vertices. "
                        + "Adjoining either isolated vertex to a cycle edge gives a triple "
                        + "with exactly one edge. These two triples exhaust the capacity "
                        + "of that edge, determining the entire family outside the pivot."))),
                DescribeRole.Theorem)),
        []));
}

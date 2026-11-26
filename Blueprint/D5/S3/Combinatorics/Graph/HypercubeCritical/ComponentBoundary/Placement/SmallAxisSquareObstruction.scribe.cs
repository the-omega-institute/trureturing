using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement;

internal sealed class SmallAxisSquareObstructionDocument : IScribeDocumentDefinition
{
    private const string Placement =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/";
    private const string Owner = Placement + "SmallAxisSquareObstruction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Square completion at cubic neighbors forces a complete bipartite graph.",
        H("Complete bipartite structure from square completion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("complete-bipartite"),
                DeclarationHandle.Create(Owner + "complete_bipartite"),
                H("Square completion and bipartite structure"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At a distinguished vertex with two nonneighbors, square completion forces each cubic neighbor to use both nonneighbors. The degree and cardinality hypotheses then identify the complete bipartite graph."))),
                DescribeRole.Theorem)),
        []));
}

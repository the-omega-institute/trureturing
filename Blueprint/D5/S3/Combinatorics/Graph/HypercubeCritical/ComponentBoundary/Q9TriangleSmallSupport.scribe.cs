using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class Q9TriangleSmallSupportDocument : IScribeDocumentDefinition
{
    private const string Module =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9TriangleSmallSupport";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Small triangle supports lie on four vertices",
        H("Small triangle supports lie on four vertices"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("q9-small-triangle-support"),
                DeclarationHandle.Create(Module + ".carried_by_four"),
                H("Small triangle supports lie on four vertices"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The absence of an edge with exactly one coface forces low-order triangle "
                        + "supports to lie on a tetrahedron boundary. Finite relabeling via an "
                        + "embedding into five vertices preserves the edge coface counts."))),
                DescribeRole.Theorem)),
        []));
}

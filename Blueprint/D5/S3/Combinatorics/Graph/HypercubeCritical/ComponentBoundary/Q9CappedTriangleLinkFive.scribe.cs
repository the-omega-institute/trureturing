using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class Q9CappedTriangleLinkFiveDocument : IScribeDocumentDefinition
{
    private const string Module =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9CappedTriangleLinkFive";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Capped triangle links on five vertices",
        H("Capped triangle links on five vertices"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("q9-triangular-bipyramid-link"),
                DeclarationHandle.Create(Module + ".triangular_bipyramid"),
                H("The triangular bipyramid"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "On five vertices, the complementary edges of the triangles form "
                        + "a complete multipartite graph. The four-set cap bounds its "
                        + "degrees by three, giving a partition into parts of sizes two "
                        + "and three. Each triangle contains one of the two apices and "
                        + "an edge of the common base."))),
                DescribeRole.Theorem)),
        []));
}

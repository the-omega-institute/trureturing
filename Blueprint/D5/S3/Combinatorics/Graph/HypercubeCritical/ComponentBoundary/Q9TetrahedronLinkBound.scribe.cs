using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class Q9TetrahedronLinkBoundDocument : IScribeDocumentDefinition
{
    private const string Module =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9TetrahedronLinkBound";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Incidence bound for capped tetrahedral supports",
        H("Incidence bound for capped tetrahedral supports"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("q9-tetrahedron-support-incidence"),
                DeclarationHandle.Create(Module + ".support_card_bound"),
                H("Incidence bound for capped tetrahedral supports"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A triangle can never have a single coface in the support of an oriented cycle. The "
                        + "vertex link therefore has no edge contained in exactly one triangle.")),
                    Paragraph(Text(
                        "In a link with at most five triangles every used vertex belongs to at least three "
                        + "of them, so the link uses at most five vertices. Complementary edges give a "
                        + "complete multipartite graph and the only nonempty cycle of this size is a "
                        + "tetrahedron boundary. The five-set cap excludes it. Counting all incidences gives "
                        + "at least six per used vertex."))),
                DescribeRole.Theorem)),
        []));
}

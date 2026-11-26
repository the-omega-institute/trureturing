using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class Q9ShellTetrahedronCycleDocument : IScribeDocumentDefinition
{
    private const string Module =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9ShellTetrahedronCycle";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The minimum capped tetrahedral cycle",
        H("Minimum order, equality and the ten-facet gap"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("q9-tetrahedral-cycle-nine"),
                DeclarationHandle.Create(Module + ".nine_le_card_tetrahedron_cycle"),
                H("At least nine tetrahedra"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The vertex links are mod-two triangle cycles. Each nonempty link has even "
                        + "size and a four-triangle link would be a tetrahedron boundary. Adding "
                        + "the linked vertex would put four selected tetrahedra in one five-set.")),
                    Paragraph(Text(
                        "There are at least six used vertices and at least six tetrahedra through "
                        + "each of them. Counting vertex incidences gives at least nine tetrahedra."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("q9-tetrahedral-cycle-equality"),
                DeclarationHandle.Create(Module + ".tetrahedron_cycle_equality"),
                H("The equality case"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "With nine tetrahedra there are six used vertices. Complement the "
                        + "tetrahedra among those six vertices and read the complementary pairs "
                        + "as edges. Each triple contains an even number of edges, so the graph "
                        + "is a cut. Its nine edges give two parts of size three.")),
                    Paragraph(Text(
                        "This cycle arises from the complement of a translated four-element shell "
                        + "of paired fibres in Hong, Wu and Xia's Problem 2. "
                        + "https://arxiv.org/html/2610.09483v1#Thmproblem2"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("q9-tetrahedral-cycle-ten-gap"),
                DeclarationHandle.Create(Module + ".ten_ne_card_tetrahedron_cycle"),
                H("Ten tetrahedra are impossible"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The incidence bound confines an order-ten cycle to six used vertices. "
                        + "The complementary graph would be a cut with ten edges, "
                        + "but the largest cut on six vertices has nine edges."))),
                DescribeRole.Theorem)),
        []));
}

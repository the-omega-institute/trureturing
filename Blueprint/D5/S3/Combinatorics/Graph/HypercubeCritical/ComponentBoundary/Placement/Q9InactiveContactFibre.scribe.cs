using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement;

internal sealed class Q9InactiveContactFibreDocument : IScribeDocumentDefinition
{
    private const string Placement =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/";
    private const string Fibre = Placement + "Q9InactiveContactFibre.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Forbidden parity corrections constrain how the two components can occupy adjacent fibres.",
        H("Five-dimensional fibres of the triangle-complement contact graph"),
        Blocks(
            Paragraph(Text("In the seven-axis triangle-complement case of Hong, Wu and Xia's Problem 2, freeze the four clique axes. The three independent active axes and the two inactive axes remain free. The sixteen fibres are indexed by the four-cube. https://arxiv.org/html/2610.09483v1#Thmproblem2")),
            Describe.Lean(
                DescribeId.Create("q9-adjacent-fibre-packing"),
                DeclarationHandle.Create(Fibre + "adjacent_fibre_capacity"),
                H("Forbidden translations pack into the adjacent fibre"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A flip of the frozen axis moves to the adjacent fibre. Each forbidden free-axis correction restores the chosen parity and sends occupied points into positions excluded from the opposite component. Two different corrections differ by the involution that flips both free axes."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("q9-five-axis-fibre-counts"),
                DeclarationHandle.Create(Fibre + "five_axis_fibre_counts"),
                H("At most eleven mixed fibres and at least five occupied pure fibres"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("A mixed fibre holds at most six points on the chosen parity. An occupied pure fibre adjacent to a mixed fibre has at least two holes because a point of the opposite component forbids two distinct positions.")),
                    Paragraph(Text("With twelve mixed fibres, each of the four remaining patterns has a mixed neighbour. The capacity is at most 12 times 6 plus 4 times 14, which is 128. With eleven mixed fibres, at most one of the other five patterns has all four neighbours among those five. Four occupied pure fibres can then contribute at most 16 plus 3 times 14, which again falls short of 129 after adding the mixed capacity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("q9-mixed-fibre-edge-capacity"),
                DeclarationHandle.Create(Fibre + "mixed_five_axis_fibre_edge_capacity"),
                H("A mixed fibre contributes at most fifteen edges in the free directions"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("A fibre with at most five occupied points on the chosen parity contributes at most fifteen edges by the degree bound. At occupancy six, the two components contribute one and five points. The five points are the free-coordinate neighbours of the singleton's antipode.")),
                    Paragraph(Text("The antipode has five selected neighbours and is excluded by the degree bound. Each remaining edge from those five points comes from a selected double flip of the antipode. Signed flip anticommutation puts the two corresponding directions in opposite sign classes. Among five directions there are at most twelve ordered pairs across those classes, and the singleton contributes at most three more edges."))),
                DescribeRole.Theorem)),
        []));
}

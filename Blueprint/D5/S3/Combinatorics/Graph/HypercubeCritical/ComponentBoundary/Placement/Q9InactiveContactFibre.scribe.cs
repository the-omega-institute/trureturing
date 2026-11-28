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
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("q9-five-pure-forces-eleven-mixed"),
                DeclarationHandle.Create(Placement + "Q9PureFibreEdgeCapacity.five_pure_contact_fibres_force_eleven_mixed"),
                H("Five occupied pure fibres force eleven mixed fibres"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Cubic regularity puts 129 selected vertices on each parity. The equal direction counts give 43 edges per axis and 215 edges in the five free directions.")),
                    Paragraph(Text("If exactly five fibres are occupied and pure and at most ten are mixed, the pure fibres have at most eleven holes in total. At least four of them adjoin a mixed fibre and therefore have at least two holes. With up to three holes in a pure fibre, any selected vertex of the opposite parity must neighbour at least two holes. Two holes have at most two common neighbours. Three holes have at most four distinct vertices adjacent to two of them, because any three intersecting pairs of their neighbourhoods have a common vertex.")),
                    Paragraph(Text("The resulting capacity of the pure fibres is at most sixty free edges. The mixed fibres contribute at most 150, so the total falls short of 215."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("q9-five-axis-hole-energy"),
                DeclarationHandle.Create(Placement + "Q9PureFibreEdgeCapacity.five_axis_hole_energy"),
                H("The signed energy bounds free edges by the parity holes"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For a balanced component in a five-axis fibre, write n for the selected size on the chosen parity, q for the opposite selected size, and e for the number of free edges. Balancing the two constant weights in the signed cut inequality gives a bound of n times q for the sum of squared directional crossing counts. Cauchy–Schwarz then gives e squared at most five times n times q.")),
                    Paragraph(Text("If there are h holes on the chosen parity, the five free neighbours of each selected opposite vertex contribute either an edge or a hole incidence. There are at most five times h hole incidences. Hence q is at most h plus the integer quotient of e by five."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("q9-five-axis-hole-linear"),
                DeclarationHandle.Create(Placement + "Q9PureFibreEdgeCapacity.five_axis_hole_linear_bound"),
                H("A linear free-edge bound in the number of holes"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Small hole counts use the common-neighbour bound. At four to six holes the energy inequality controls the finite range left by subcubic degree. The degree bound suffices for larger hole counts. In particular the total is at most five times the number of holes plus one, and at six holes it is at most twenty-two."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("q9-five-axis-forbidden-eight"),
                DeclarationHandle.Create(Placement + "Q9FiveAxisExcessCycles.no_mapped_excess"),
                H("An eight-cycle rules out the local four- and five-hole excesses"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("In the five-bit representation, place the forbidden odd vertex at word eight and its two forced even holes at words zero and twenty-four. Enumerate the remaining holes and the opposite vertices with positive free degree at most three. After removing squares and hexagons, every support exceeding fourteen edges at four holes or nineteen edges at five holes contains the two four-step paths of the same eight-cycle type.")),
                    Paragraph(Text("A representation respecting coordinate flips carries those two paths into the selected support. Their flip words have the same endpoint. Anticommuting the signed flip operators puts their products in opposite signs, contradicting balance."))),
                DescribeRole.Theorem)),
        []));
}

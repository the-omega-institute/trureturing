using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class HuangThreeColumnIntegralityDocument : IScribeDocumentDefinition
{
    private const string Module =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/HuangThreeColumnIntegrality";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Even coefficients for three signed cube columns",
        H("Even coefficients for three signed cube columns"),
        Blocks(
            Paragraph(Text("In the 18+3 fold for Hong–Wu–Xia Problem 2, the three opposite dimers give signed Huang columns B on the folded eight-cube. Each column has at least four neighbors among the empty rows R. At unit transverse weights the leading balance equation on those rows is Bc + f_R = 0, with residual f = HΛHb. Modulo two the signed flips become unsigned adjacency and the diagonal signs in Λ become one. The residual reduces to A² applied to the indicator of the occupied dimers. BinaryKernelCoordinateMoment.adjacency_adjacency_eq_zero gives A² = 0 in dimension eight, so Bc is even on R and the three real amplitudes c are even integers. The problem appears in arXiv:2610.09483v1, Section 7 (https://arxiv.org/html/2610.09483v1#Thmproblem2).")),
            Describe.Lean(
                DescribeId.Create("even-coefficients-of-three-cube-columns"),
                DeclarationHandle.Create(Module + ".even_coefficients_of_three_cube_columns"),
                H("Even row sums force even coefficients"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Vertices are finite coordinate sets and nearest neighbors differ by one coordinate. Choose three distinct centers and one common finite set of rows. Each column is zero off its center's neighbors on those rows and has entry 1 or −1 at every included neighbor. Assume each column has at least four such entries.")),
                    Paragraph(Text("Distinct centers with a common neighbor differ in two coordinates and can share only the two corresponding flips. If all three pairs share a neighbor, translate one center to the empty set. The other two centers are distinct two-element sets whose symmetric difference has size two. Their common coordinate gives a neighbor of all three centers. The two pairwise intersections at the first center therefore have union of size at most three. If some pair shares no neighbor, one center of that pair has at most two neighbors in the union of the other columns.")),
                    Paragraph(Text("A row belonging to just one column determines its amplitude up to sign. Subtracting that column's contribution preserves evenness of every row. Each remaining column has a row outside the other remaining column, so both remaining amplitudes are even as well.")),
                    Paragraph(Text("Four signed Huang columns can admit half-integer amplitudes. Take four singleton centers and retain the empty vertex and the six two-element vertices on their axes. Each column has four entries. Normalize the column signs so each entry at the empty vertex is +1. The two entries on each pair row are opposite by anticommutation of the two signed flips, so a zero target on every pair row forces all four amplitudes equal. Target 2 at the empty vertex then forces each amplitude to be 1/2."))),
                DescribeRole.Theorem)),
        []));
}

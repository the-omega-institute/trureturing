using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves;

internal sealed class BalancedHalfCardinalityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "BalancedHalfCardinality", H("Size and parity of balanced cubic coordinate halves"),
        Blocks(Describe.Lean(
            DescribeId.Create("balanced-half-cardinality"),
            DeclarationHandle.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BalancedHalfCardinality.half_cardinality"),
            H("The cut size controls the cardinality of each half"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("In a Huang-balanced cubic support of order six times q in the nine-cube, "
                    + "each coordinate cut has q edges. Each half has exactly q degree-two vertices, "
                    + "and those vertices are independent.")),
                Paragraph(Text("The two edges at each degree-two vertex enter the cubic vertices of the half. "
                    + "Counting those incidences gives the lower bound of five thirds of q. "
                    + "The equal degree sums on the two bipartition classes give the parity of q.")),
                Paragraph(Text("For an order-72 component in a candidate for Hong–Wu–Xia's Problem 2, "
                    + "the half must have even cardinality and at least twenty vertices."))),
            DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeLowerBound")),
         DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S3/Combinatorics/Graph/HypercubeCritical/CubicFiftyFourReconstruction"))]));
}

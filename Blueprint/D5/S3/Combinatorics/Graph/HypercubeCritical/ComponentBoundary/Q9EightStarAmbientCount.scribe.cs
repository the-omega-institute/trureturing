using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class Q9EightStarAmbientCountDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9EightStarAmbientCount";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ambient size constraint of the eight-star",
        H("Ambient size constraint of the eight-star"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("eight-star-third-vertices"),
                DeclarationHandle.Create(Module + ".eight_star_ambient_count"),
                H("Two disjoint sixteen-vertex families"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The sixteen lifted spokes and the third neighbors of the sixteen selected mixed corners lie in one projected parity. A repeated third neighbor would form a selected square, violating balance."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("eight-star-ten-pairs"),
                DeclarationHandle.Create(Module + ".directionEdges_ge_ten_of_eight_star"),
                H("Eight-star completion requires at least ten paired fibres"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The occupied-fibre identity gives three times the projected-parity vertex count as eight times the paired count plus twice its parity part. The thirty-two vertices force a paired count of at least ten."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/PrimeContactCardinalityGap")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9OccupiedFibreParity"))]));
}

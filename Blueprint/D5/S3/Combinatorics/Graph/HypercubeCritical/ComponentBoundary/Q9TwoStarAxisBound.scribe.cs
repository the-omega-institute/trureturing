using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class Q9TwoStarAxisBoundDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9TwoStarAxisBound";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two-axis eight-star geometry",
        H("Two-axis eight-star geometry"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("two-star-twelve-paired-edges"),
                DeclarationHandle.Create(Module + ".directionEdges_ge_twelve_of_two_stars"),
                H("Twelve edges in the second direction"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A full eight-star on one axis supplies four edges along each transverse axis. If one of these were a spoke of another star, commuting flips would force a selected center or a forbidden same-part corner in the first star. These four edges and the eight spokes are disjoint."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("two-star-component-size"),
                DeclarationHandle.Create(Module + ".card_ge_seventy_two_of_two_stars"),
                H("Component order at least seventy-two"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Huang balance and cubicity give equal direction counts. The two-axis geometric bound therefore gives a lower bound of 72 vertices in an actual component for Hong–Wu–Xia Problem 2. https://arxiv.org/html/2610.09483v1#Thmproblem2"))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9OccupiedFibreParity"))]));
}

using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement;

internal sealed class Q9ActualMinimumDisplacementsDocument : IScribeDocumentDefinition
{
    private const string Cube = "D5/S3/Combinatorics/Graph/HypercubeCritical/";
    private const string Placement = Cube + "ComponentBoundary/Placement/";
    private const string Owner = Placement + "Q9ActualMinimumDisplacements.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Minimum displacements of actual components in the nine-cube problem.",
        H("The same two components supply both parities"),
        Blocks(Describe.Lean(
            DescribeId.Create("q9-two-actual-components-minimum-displacement-bound"),
            DeclarationHandle.Create(Owner + "exists_two_components_with_minimum_displacement_bound"),
            H("Minimum distance and displacement bounds for a 258-point support"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Choose two actual components with universally singular weighted "
                    + "defects. The minimum distance between this pair is two, three, or four. "
                    + "On each starting parity that realizes that distance, there are at least "
                    + "six, ten, or fifteen distinct displacements, respectively. At equality "
                    + "the displacements are all the subsets of the required size on a common "
                    + "set of two more axes.")),
                Paragraph(Text("The positive Gram eigenvalue transfers to the opposite parity "
                    + "by multiplying its eigenvector by the transpose of the signed "
                    + "biadjacency. The transpose is the other parity's signed biadjacency "
                    + "after reindexing. Positivity and connectedness then supply an ambient "
                    + "vector with full support on whichever parity the distance requires. "
                    + "Thus the minimum distance, both parity sides, and the independently "
                    + "chosen weightings refer to the same pair of components. "
                    + "<https://arxiv.org/html/2610.09483v1#Thmproblem2>"))),
            DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create(Placement + "CubicContactDistance")),
         DocumentEdge.Dependency.Create(GidRef.Create(Placement + "Q9MinimumDistanceOperator")),
         DocumentEdge.Dependency.Create(GidRef.Create(Placement + "Q9SaturatedContactCompanions")),
         DocumentEdge.Dependency.Create(GidRef.Create(Cube + "Translation/Q9TranslationAperiodicity"))]));
}

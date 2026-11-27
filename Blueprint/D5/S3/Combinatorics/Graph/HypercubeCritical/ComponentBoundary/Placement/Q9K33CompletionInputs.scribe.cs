using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement;

internal sealed class Q9K33CompletionInputsDocument : IScribeDocumentDefinition
{
    private const string Owner =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9K33CompletionInputs.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two-coordinate saturation forces a corner and ambient packing forces sixty vertices.",
        H("Size and direction pairs in actual components"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("exists-corner-for-each-direction-pair"),
                DeclarationHandle.Create(Owner + "exists_corner_for_each_direction_pair"),
                H("Every pair of directions occurs at a common corner"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Put unit weight on the two prescribed axes and zero elsewhere. The singular defect forces a row whose selected incident weights sum to at least the square root of two. Both directions must therefore lead into the component."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sixty-le-actual-component"),
                DeclarationHandle.Create(Owner + "sixty_le_actual_component"),
                H("An actual component has at least sixty vertices"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The balanced cubic lower bound starts at fifty-four. A closed component of size fifty-four limits the ambient subcubic set to 257. Each axis contributes one sixth of the component size, so the next available size is sixty."))), DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeFiftyFourLowerBound")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9ComponentWeightedProfile")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9Gray54ExtensionBound"))
        ]));
}

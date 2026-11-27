using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement;

internal sealed class Q9FiveAxisMissingContactDocument : IScribeDocumentDefinition
{
    private const string Placement =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/";
    private const string Owner = Placement + "Q9FiveAxisMissingContact.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Normalize a realized eight-mask contact by the cube isometry group.",
        H("One orbit of chosen eight-mask contacts"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("exists-normalized-eight-mask-contact"),
                DeclarationHandle.Create(Owner + "exists_normalized_eight_mask_contact"),
                H("One orbit of chosen eight-mask contacts"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The eight-mask graph is a complete five-axis graph with two disjoint edges deleted. Its unique degree-four axis belongs to a realized contact. Translation sends the left endpoint to zero, and the axis permutation sends the chosen edge to {0, 1} and the two deleted edges to {1, 2} and {3, 4}. This gives a single configuration for the refutation."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(Placement + "Q9TightDistanceTwoNormalized"))
        ]));
}

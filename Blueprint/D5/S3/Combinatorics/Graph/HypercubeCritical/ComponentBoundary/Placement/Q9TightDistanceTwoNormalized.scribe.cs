using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement;

internal sealed class Q9TightDistanceTwoNormalizedDocument : IScribeDocumentDefinition
{
    private const string Placement =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/";
    private const string Owner = Placement + "Q9TightDistanceTwoNormalized.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cube translations and axis permutations give two opposing-star cases for tight distance-two contact.",
        H("The two orbits of the missing directions"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("exists-normalized-tight-distance-two"),
                DeclarationHandle.Create(Owner + "exists_normalized_tight_distance_two"),
                H("The two orbits of the missing directions"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Translate the first star center to zero and move the four internal axes to the first four positions. The remaining coordinate permutations act on the two ordered missing directions. Equality of those directions gives one orbit and distinct directions give the other. The action transports the entire displacement family of the relevant parity together with the local degree and square conditions."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(Placement + "Q9TightDistanceTwoCenter")),
            DocumentEdge.Dependency.Create(GidRef.Create(Placement + "Q9SharedContactNormalized"))
        ]));
}

using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class Q9SignedCoordinateCongruenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SignedCoordinateCongruence.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed two-step and three-step contacts",
        H("Signed two-step and three-step contacts"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("q9-signed-coordinate-congruence"),
                DeclarationHandle.Create(Prefix + "signedPairingInt_triangle_mod3"),
                H("Signed two-step and three-step contacts"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Extend the two component switching functions by zero and pair them "
                        + "through actual Huang coordinate actions.")),
                    Paragraph(Text("Anticommuting the sum of coordinate flips past a triple of flips "
                        + "gives a signed sum of the three pairings on its coordinate pairs. The "
                        + "eigenvalue three makes that sum divisible by three. For separated "
                        + "supports the pairings also have zero row sums.")),
                    Paragraph(Text("These congruences constrain distance-two contacts according to their "
                        + "differing coordinates and signs."))),
                DescribeRole.Theorem)),
        []));
}

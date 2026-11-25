using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves;

internal sealed class Q9ThreeAxisCapacityTransportDocument : IScribeDocumentDefinition
{
    private const string Root = "D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Four-face packing in subcubic nine-cube supports",
        H("Capacity of a witnessed face"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("two-actual-components-have-distinct-witness-faces"),
                DeclarationHandle.Create(Root + "Q9ThreeAxisCapacityTransport.two_components_four_face_capacity"),
                H("Two actual components force distinct four-faces"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Choose the two actual components of a 258-point subcubic support before choosing four active coordinates. For each dominant axis, fix one projected parity per component before the transverse mask. Each witness face is anchored at an actual paired vertex of that parity. On the other three axes a masked boundary kernel restricts to a three-cube slice.")),
                    Paragraph(Text("The full parity block on that slice is orthogonal up to the squared weight norm. Its unique zero in each row and column is the antipodal position. This forces a rank-deficient restriction to have more paired columns than empty rows, a retained antipodal singleton pair, or an omitted antipodal pair in the three-by-three case.")),
                    Paragraph(Text("Restore the dominant axis. In each witness case the complement of the component's closed neighborhood has at most three vertices in the four-face. Every other selected component therefore has to share those three places. A rank witness needs at least five vertices, so the two selected components require different four-faces for the same mask.")),
                    Paragraph(Text("These are necessary conditions for a 258-point subcubic support in Hong, Wu and Xia's Problem 2. The four-face labels are the five inactive bits, which also show how the capacity constraints move under XOR translations. https://arxiv.org/html/2610.09483v1#Thmproblem2"))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(Root + "Q9DominantAxisBoundary")),
            DocumentEdge.Dependency.Create(GidRef.Create(Root + "Q9FourFaceDefect"))
        ]));
}

using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.FundamentalBijection;

internal sealed class ThetaIterateEndpointShapeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/FundamentalBijection/ThetaIterateEndpointShape.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/archer2024fundamental");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The final-maximum family consists of two explicit words and a cyclic family.",
        H("Shape of Parameters with a Final Maximum"),
        Blocks(
            Node("fundamental-bijection-thetaiterateendpointshape-last-endpoint-shape", "The three possible shapes", "last_endpoint_shape",
                "For a stem permutation r of size h at least three, P of r followed by h plus one avoids 132 through depth two exactly when r is increasing, r is two through h followed by one, or r begins with h and ends with one and its inverse fundamental image avoids 132 through depth two.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}

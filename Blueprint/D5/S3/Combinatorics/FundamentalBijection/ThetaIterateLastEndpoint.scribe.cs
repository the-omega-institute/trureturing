using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.FundamentalBijection;

internal sealed class ThetaIterateLastEndpointDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/FundamentalBijection/ThetaIterateLastEndpoint.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/archer2024fundamental");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A final-maximum parameter reduces to the inverse image of its stem.",
        H("Cycle Reduction at a Final Maximum"),
        Blocks(
            Node("fundamental-bijection-thetaiteratelastendpoint-last-endpoint-cycle", "The stem and its inverse image", "last_endpoint_cycle",
                "For a stem r of size h at least two beginning with h, depth-two avoidance of P of r followed by h plus one forces r to end with one. If r ends with one, its inverse fundamental image begins with h and has fundamental image r, and the P construction avoids through depth two exactly when that inverse image does.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}

using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.FundamentalBijection;

internal sealed class ThetaIterateEndpointCountDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/FundamentalBijection/ThetaIterateEndpointCount.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/archer2024fundamental");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Parameters ending at their maximum are counted by a smaller family beginning at its maximum.",
        H("Counting Parameters with a Final Maximum"),
        Blocks(
            Node("fundamental-bijection-thetaiterateendpointcount-last-endpoint-count", "The final-maximum parameter count", "last_endpoint_count",
                "For n at least two, the number of parameter permutations of size n plus one ending with n plus one whose P images avoid 132 through depth two equals one plus the number of depth-two avoiders of size n beginning with n.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}

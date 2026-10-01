using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.FundamentalBijection;

internal sealed class ThetaIterateEndpointsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/FundamentalBijection/ThetaIterateEndpoints.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/archer2024fundamental");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The maximum of an eligible parameter lies at exactly one endpoint.",
        H("Location of the Parameter Maximum"),
        Blocks(
            Node("fundamental-bijection-thetaiterateendpoints-parameter-endpoints", "Exactly one maximal endpoint", "parameter_endpoints",
                "A parameter permutation of size at least two whose P image avoids 132 through depth two has its maximum at its first or last position, but not at both.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}

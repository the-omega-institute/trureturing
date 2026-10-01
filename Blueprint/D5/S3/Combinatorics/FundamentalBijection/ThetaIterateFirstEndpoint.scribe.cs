using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.FundamentalBijection;

internal sealed class ThetaIterateFirstEndpointDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/FundamentalBijection/ThetaIterateFirstEndpoint.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/archer2024fundamental");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A maximal first letter and a terminal one force a descending parameter when its successor word avoids 132.",
        H("A Descending Parameter at the First Endpoint"),
        Blocks(
            Node("fundamental-bijection-thetaiteratefirstendpoint-descending-of-last-one-and-b-avoids", "The descending permutation", "descending_of_last_one_and_b_avoids",
                "A permutation of size at least two beginning with its maximum and ending with one is decreasing if its successor word b avoids 132.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}

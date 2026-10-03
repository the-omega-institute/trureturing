using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.FundamentalBijection;

internal sealed class ThetaIterateUFamiliesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/FundamentalBijection/ThetaIterateUFamilies.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/archer2024fundamental");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A maximal first letter followed by an increasing tail gives an explicit eligible parameter.",
        H("The Increasing Tail Family"),
        Blocks(
            Node("fundamental-bijection-thetaiterateufamilies-u", "A maximum followed by an increasing tail", "U",
                "The word U(h) is h followed by one through h minus one.", DescribeRole.Definition),
            Node("fundamental-bijection-thetaiterateufamilies-u-family", "Images and characterization of the increasing tail", "U_family",
                "For h at least four, U(h) permutes one through h, its fundamental image is decreasing, its successor word is three through h followed by one and two, and its cycle from h equals its fundamental image. Among first-maximum parameters whose second letter is at most h minus two, the P construction avoids 132 through depth two exactly for U(h).", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}

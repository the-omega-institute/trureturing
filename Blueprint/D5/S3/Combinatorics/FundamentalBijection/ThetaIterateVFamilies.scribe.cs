using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.FundamentalBijection;

internal sealed class ThetaIterateVFamiliesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/FundamentalBijection/ThetaIterateVFamilies.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/archer2024fundamental");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The decreasing word has an explicit fundamental image and characterizes parameters ending with one.",
        H("The Descending Parameter Family"),
        Blocks(
            Node("fundamental-bijection-thetaiteratevfamilies-v-family", "The decreasing family and its later orbit", "V_family",
                "For h at least two, the fundamental image of the decreasing word begins with h divided by two plus one when h is odd, then consists of pairs x, h plus one minus x for increasing x from the integer part of h divided by two plus one plus the parity of h through h. Its successor word is increasing. Among parameters beginning with h and ending with one, P avoids 132 through depth two exactly for the decreasing parameter. For h at least four, the second fundamental image of that decreasing parameter contains 132.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}

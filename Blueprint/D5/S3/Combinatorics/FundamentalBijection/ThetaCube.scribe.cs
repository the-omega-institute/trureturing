using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.FundamentalBijection;

internal sealed class ThetaCubeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/FundamentalBijection/ThetaCube.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/archer2024fundamental");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The generating functions for 231- and 312-avoiders fixed by the third iterate of the fundamental bijection are rational.",
        H("Fixed Avoiders of the Third Iterate"),
        Blocks(
            Node("fundamental-bijection-thetacube-result", "The third-iterate generating function", "result",
                "For each pattern sigma equal to 231 or 312, the ordinary generating function for sigma-avoiding permutations fixed by the third iterate of the fundamental bijection, multiplied by 1 - x - x squared - 2x cubed, equals one.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}

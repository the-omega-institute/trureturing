using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.FundamentalBijection;

internal sealed class ThetaIterateDecompositionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/FundamentalBijection/ThetaIterateDecomposition.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/archer2024fundamental");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The second avoidance layer splits into a cycle family and two exceptional permutations.",
        H("Decomposition of the Second Avoidance Layer"),
        Blocks(
            Node("fundamental-bijection-thetaiteratedecomposition-second-layer-decomposition", "The families beginning or not ending at the maximum", "second_layer_decomposition",
                "For size n at least four, the second-layer avoiders beginning with n are the image under P of eligible parameter permutations of size n minus two together with n, two, three, up to n minus one, one; their number is the parameter count plus one. The second-layer avoiders not ending with n consist of this family together with two, three, up to n, one; their number is the parameter count plus two.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}

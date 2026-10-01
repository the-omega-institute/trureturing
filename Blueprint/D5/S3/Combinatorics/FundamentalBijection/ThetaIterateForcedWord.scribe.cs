using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.FundamentalBijection;

internal sealed class ThetaIterateForcedWordDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/FundamentalBijection/ThetaIterateForcedWord.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/archer2024fundamental");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "First-maximum parameters fall into explicit families or a recursively inserted cycle family.",
        H("Classification at the First Endpoint"),
        Blocks(
            Node("fundamental-bijection-thetaiterateforcedword-w", "The balanced two-block word", "W",
                "For size h and a equal to the integer part of (h plus one) divided by two, W(h) consists of h down to a plus one, then a minus one down to one, then a.", DescribeRole.Definition),
            Node("fundamental-bijection-thetaiterateforcedword-first-endpoint-classification", "Explicit words and recursive insertion", "first_endpoint_classification",
                "Let r be a permutation of size h at least four beginning with h, and suppose r, b(r), and its fundamental image avoid 132. Then r is U(h), is decreasing, or begins with h, h minus one, has penultimate value one and terminal value v between two and h minus two, and has its cycle from h equal to its fundamental image. In the third case v below h minus two forces r = W(h); when v = h minus two and h is at least five, r has a unique representation as I of a first-maximum parameter of size h minus three whose P image avoids through depth two and whose cycle from its maximum equals its fundamental image.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}

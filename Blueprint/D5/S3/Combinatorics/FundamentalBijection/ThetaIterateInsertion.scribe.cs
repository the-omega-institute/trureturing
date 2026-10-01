using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.FundamentalBijection;

internal sealed class ThetaIterateInsertionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/FundamentalBijection/ThetaIterateInsertion.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/archer2024fundamental");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A three-letter insertion preserves two avoidance conditions and has a unique inverse on its specified boundary shape.",
        H("Insertion of Three Letters"),
        Blocks(
            Node("fundamental-bijection-thetaiterateinsertion-i", "The three-letter insertion", "I",
                "For a parameter of length h, I places h plus three and h plus two first, increases each parameter letter after the first by one, and finishes with one and h plus one.", DescribeRole.Definition),
            Node("fundamental-bijection-thetaiterateinsertion-insertion-scan", "The successor word and avoidance after insertion", "insertion_scan",
                "For a first-maximum parameter r of length h at least two, I(r) is a permutation of size h plus three. Its successor word is h plus two, the first h minus one entries of b(r) increased by one, one, the last entry of b(r) increased by one, and h plus three. Avoidance of 132 by r and by b(r) is respectively equivalent to avoidance by I(r) and by b(I(r)). Every permutation of size h plus three beginning with h plus three, h plus two and ending with one, h plus one has a unique first-maximum parameter preimage under I.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}

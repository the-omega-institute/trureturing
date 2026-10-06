using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.MetallicHankel;

internal sealed class MetallicHankelTransferDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/MetallicHankel/MetallicHankelTransfer.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/han2025hankel");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The metallic transfer word returns the pair (1,0) after each cycle and bounds both coordinates by the set {-1,0,1,2}.",
        H("The Two-Coordinate Metallic Transfer"),
        Blocks(
            Node("metallic-hankel-transfer-top-word", "The ordered transfer coefficients", "topWord",
                "At n = 2 the word of pairs (d,b) is (2,-1),(0,1),(0,-1),(1,-1),(0,-1),(0,-1),(2,1),(-1,-1). For every other nonnegative n it starts with (2,-1),(0,1), contains n-2 copies of the triple (1,-1),(1,-1),(-1,-1), then (0,-1),(1,-1),(0,-1),(-1,-1), then n-3 copies of the same triple, and ends with (1,-1),(1,-1),(0,-1),(2,1),(-1,-1). Repetition counts use natural subtraction truncated at zero.", DescribeRole.Definition),
            Node("metallic-hankel-transfer-block", "Periodicity and bounds of the transfer coordinates", "block_transfer",
                "Let n be at least two, let W be its transfer word of length L, and let z_p be a sequence of integer pairs with z_0 = (1,0). If W at position p modulo L is (d,b), require z_{p+1} = (d x - b y,x), where z_p = (x,y). Then for every nonnegative p, z_{p+L} = z_p and both coordinates of z_p belong to {-1,0,1,2}. Repeated triples and the two end segments give the return and the bounds at every intermediate position.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}

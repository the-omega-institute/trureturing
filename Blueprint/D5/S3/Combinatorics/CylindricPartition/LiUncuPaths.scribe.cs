using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.CylindricPartition;

internal sealed class LiUncuPathsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/CylindricPartition/LiUncuPaths.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/li2025macmahon");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The sum of peak abscissae gives a polynomial weight on paths with horizontal edges only at the floor.",
        H("Weighted Paths in a Bounded Strip"),
        Blocks(
            Node("li-uncu-paths-pathpolynomial", "The path polynomial", "pathPolynomial",
                "For nonnegative integers H and L and integer endpoints a and b, the polynomial sums q raised to peakWeight(0,w) over all valid words w of length L from height a to height b in the strip from zero to H. Invalid words contribute zero.", DescribeRole.Definition),
            Node("li-uncu-paths-path-last-edge-recurrence", "The last-edge recurrence", "path_last_edge_recurrence",
                "Write P(L,a,b) for the path polynomial at height bound H. For H at least one and an integer b between zero and H, P(L+2,a,b) = P(L+1,a,b-1) when b = H. Otherwise it equals P(L+1,a,c) + P(L+1,a,b+1) + (q^(L+1) - 1) P(L,a,b), where c = 0 when b = 0 and c = b - 1 otherwise. This holds for every nonnegative L and every integer a.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}

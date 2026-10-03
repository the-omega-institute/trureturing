using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.CrosswordGrid;

internal sealed class SkewMergedRookPlacementsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/CrosswordGrid/SkewMergedRookPlacements.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/lewis2026crossword");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every permutation grid has a complete placement; overlapping increasing and decreasing covers force uniqueness.",
        H("Existence and Uniqueness of Complete Placements"),
        Blocks(
            Node("skew-merged-rook-placements-count-positive", "Existence of a complete placement", "count_positive",
                "For every positive integer n and every permutation w of zero through n minus one, the number of complete rook placements of its permutation grid is strictly positive.", DescribeRole.Theorem),
            Node("skew-merged-rook-placements-overlapping-count", "An overlapping monotone cover", "overlapping_count",
                "Let n be positive and let two sets of positions cover all positions of a permutation w. Suppose that the values on the first set increase with position and the values on the second set decrease with position. If some position belongs to both sets, the permutation grid of w has exactly one complete rook placement.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}

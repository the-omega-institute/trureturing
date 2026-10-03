using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.CrosswordGrid;

internal sealed class SkewMergedRookDeletionsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/CrosswordGrid/SkewMergedRookDeletions.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/lewis2026crossword");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Adding a final maximum, or inserting an interior maximum under a specified ordering condition, cannot decrease the rook-placement count.",
        H("Placement Counts Under Extreme Insertions"),
        Blocks(
            Node("skew-merged-rook-deletions-corner-lift", "Appending a maximum", "corner_lift",
                "Let n be positive and let u be a permutation of zero through n minus one. Let w be a permutation of zero through n with w(n) equal to n and w(i) equal to u(i) for every i less than n. The number of complete rook placements of the grid of u is at most the number for the grid of w.", DescribeRole.Theorem),
            Node("skew-merged-rook-deletions-interior-lift", "Inserting an interior maximum", "interior_lift",
                "Let n be positive, let u be a permutation of zero through n minus one, and let w be a permutation of zero through n. Choose a position p strictly between zero and n with w(p) equal to n. Deleting that position from w, without changing the other values, gives u. If the position of value n minus one in w is less than p, the number of complete rook placements of the grid of u is at most the number for the grid of w.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}

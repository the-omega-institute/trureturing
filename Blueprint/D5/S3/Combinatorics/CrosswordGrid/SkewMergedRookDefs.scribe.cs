using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.CrosswordGrid;

internal sealed class SkewMergedRookDefsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/CrosswordGrid/SkewMergedRookDefs.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/lewis2026crossword");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Skew-merged permutations split into an increasing and a decreasing subsequence; their permutation grids are conjectured to have one or two complete rook placements.",
        H("Skew-Merged Permutations and Rook Placements"),
        Blocks(
            Node("skew-merged-rook-defs-skew-merged", "Increasing and decreasing subsequences", "SkewMerged",
                "Let w be a permutation of the positions zero through n minus one. It is skew-merged if there is a set S of positions such that, for any i and j in S with i less than j, w(i) is less than w(j), and, for any i and j outside S with i less than j, w(j) is less than w(i). Either subsequence may be empty.", DescribeRole.Definition),
            Node("skew-merged-rook-defs-claim", "The conjectured equivalence", "claim",
                "For every positive integer n and every permutation w of zero through n minus one, the n by n grid with black cells (i, w(i)) has exactly one or exactly two complete rook placements if and only if w is skew-merged. A complete rook placement is a set of white cells meeting each maximal horizontal white interval and each maximal vertical white interval exactly once.", DescribeRole.Definition)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}

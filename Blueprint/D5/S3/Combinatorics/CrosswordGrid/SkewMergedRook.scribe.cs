using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.CrosswordGrid;

internal sealed class SkewMergedRookDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/CrosswordGrid/SkewMergedRook.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/lewis2026crossword");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A permutation grid has exactly one or two complete rook placements if and only if its permutation is skew-merged.",
        H("Skew-Merged Permutations Are Exactly Those With One or Two Placements"),
        Blocks(
            Node("skew-merged-rook-result", "The skew-merged equivalence", "result",
                "For every positive integer n and every permutation w of zero through n minus one, the n by n grid with black cells (i, w(i)) has exactly one or exactly two complete rook placements if and only if the positions of w split into a set on which its values increase and a complementary set on which its values decrease. Complete placements meet every maximal horizontal white interval and every maximal vertical white interval exactly once. This is Conjecture 3.9 of Lewis and Won.", DescribeRole.Theorem, new OpenProblemResolutionClaim(ProblemSlugRef.Create("lewis-won-skew-merged-rook-placements"), ResolutionKind.Proved))
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}

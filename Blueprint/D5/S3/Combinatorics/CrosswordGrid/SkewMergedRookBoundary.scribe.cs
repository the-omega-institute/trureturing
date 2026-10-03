using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.CrosswordGrid;

internal sealed class SkewMergedRookBoundaryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/CrosswordGrid/SkewMergedRookBoundary.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/lewis2026crossword");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Boundary-minimal permutations that are not skew-merged have two explicit shapes up to value complementation, and the first family has at least three placements.",
        H("Boundary-Minimal Permutations and Their Placement Counts"),
        Blocks(
            Node("skew-merged-rook-boundary-minimal-classification", "Two boundary-minimal shapes", "boundary_minimal_classification",
                "Let n be positive and let w be a permutation of zero through n minus one that is not skew-merged. Suppose that every occurrence of 2143 or 3412 contains the first position, the last position, the position of value zero, and the position of value n minus one. There is a permutation s equal to w or its value complement, with positions p and q satisfying zero less than p less than q less than n minus one, s(p) equal to zero, s(q) equal to n minus one, and s(0) less than s(n - 1). For some nonnegative integers a and b, n equals a plus b plus four, and one of two shapes holds. In the first, p equals a plus one, q equals n minus two, s(0) equals one, s(n - 1) equals b plus two, s(i) plus i equals n minus one for zero less than i less than p, and s(i) equals i minus p plus one for p less than i less than q. In the second, p equals one, q equals b plus two, s(0) equals a plus one, s(n - 1) equals n minus two, s(i) equals i minus p plus s(0) for p less than i less than q, and s(i) plus i equals n minus one for q less than i less than n minus one.", DescribeRole.Theorem),
            Node("skew-merged-rook-boundary-family-count", "At least three placements in the first family", "family_count",
                "Let a and b be nonnegative integers and let n equal a plus b plus four. Suppose that the permutation w of zero through n minus one has the following values: w(0) equals one; w(i) equals n minus i minus one for one at most i at most a; w(a + 1) equals zero; w(i) equals i minus a for a plus one less than i less than a plus b plus two; w(a + b + 2) equals n minus one; and w(n - 1) equals b plus two. The permutation grid of w has at least three complete rook placements.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}

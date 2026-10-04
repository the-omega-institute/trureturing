using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.CylindricPartition;

internal sealed class LiUncuRecurrenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/CylindricPartition/LiUncuRecurrence.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QSeries/li2025macmahon");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Counting paths by deleted peaks yields a primed Gaussian recurrence, including negative virtual lengths.",
        H("Refined Path Polynomials and Deletion"),
        Blocks(
            Node("li-uncu-recurrence-pathwords", "All words of a fixed length", "pathWords",
                "For every nonnegative integer L, pathWords(L) is the finite set of all length-L words over the up, down, and horizontal alphabet. The length-zero set contains only the empty word.", DescribeRole.Definition),
            Node("li-uncu-recurrence-refinedpathsum", "The refined diagonal path sum", "refinedPathSum",
                "For nonnegative H and N and integers a and L, a nonnegative L gives the sum of q raised to peakWeight(0,w) over valid length-L paths from a to a with height bound H and exactly N pairs removed by peakData. For negative L, the value is one when N = 0 and zero otherwise.", DescribeRole.Definition),
            Node("li-uncu-recurrence-path-deletion-recurrence", "The primed Gaussian deletion recurrence", "path_deletion_recurrence",
                "Let H be at least one, let a be an integer between zero and H, let L be an even integer, and let N be nonnegative. Put beta = 1 when a = H and beta = 0 otherwise, and Lprime = L - 2N - 2beta. Then refinedPathSum(H,a,L,N) equals q^(N^2+beta N) times the sum, for s from zero through N, of the primed Gaussian polynomial with upper index Lprime + N - s and lower index N - s, multiplied by refinedPathSum(H-1,a-beta,Lprime,s).", DescribeRole.Theorem),
            Node("li-uncu-recurrence-path-zero-height", "The height-zero value", "path_zero_height",
                "For every integer L and nonnegative integer N, refinedPathSum(0,0,L,N) is one when N = 0 and zero otherwise. For nonnegative L the sole path is the horizontal word; negative L uses the same virtual value.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}

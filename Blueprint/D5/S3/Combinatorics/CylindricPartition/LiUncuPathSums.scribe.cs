using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.CylindricPartition;

internal sealed class LiUncuPathSumsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/CylindricPartition/LiUncuPathSums.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QSeries/li2025macmahon");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Insertion vectors enumerate finite sets of paths with exact Gaussian weights.",
        H("Weighted Peak-Insertion Sums"),
        Blocks(
            Node("li-uncu-path-sums-peakrequirement", "Mandatory insertion at a peak", "peakRequirement",
                "For a word q and a vertex index j counted from zero, the requirement is one precisely when the vertex lies between an up edge and the immediately following down edge. It is zero at all other indices, including indices outside the word.", DescribeRole.Definition),
            Node("li-uncu-path-sums-insertionwords", "Words with a prescribed insertion total", "insertionWords",
                "At the length(q) + 1 vertices of q, insert a total of N up-down pairs using nonnegative multiplicities at most N, with a positive multiplicity at every old peak. The resulting finite set contains the inserted words. When the boundary parameter is true, a down edge is added at the beginning and an up edge at the end.", DescribeRole.Definition),
            Node("li-uncu-path-sums-peak-deletion-weighted-sum", "The weighted insertion formula", "peak_deletion_weighted_sum",
                "Let S be any finite set of words, let N and offset be nonnegative integers, and put beta = 1 for a true boundary parameter and beta = 0 otherwise. For each word v in S, let C(v) be the number of peaks deleted by peakData. The sum of q raised to peakWeight(offset,w) over the union of insertionWords(v,N,boundary) equals q^(N^2 + (offset+beta)N) times the sum over v in S of q^peakWeight(0,v) G(length(v)+N-C(v),N-C(v)) when C(v) is at most N, and zero otherwise.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}

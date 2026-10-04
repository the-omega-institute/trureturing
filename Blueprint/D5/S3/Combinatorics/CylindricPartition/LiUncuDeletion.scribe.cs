using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.CylindricPartition;

internal sealed class LiUncuDeletionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/CylindricPartition/LiUncuDeletion.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/ArithSums/li2025macmahon");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Deleting up-down pairs gives a bijection between words and insertion data and lowers the height bound of paths.",
        H("Peak Deletion and Insertion"),
        Blocks(
            Node("li-uncu-deletion-step", "The path alphabet", "Step",
                "The alphabet consists of an up edge, a down edge, and a horizontal edge.", DescribeRole.Definition),
            Node("li-uncu-deletion-peakdata", "Deletion data", "peakData",
                "Scan a word from left to right and delete every adjacent up-down pair. The output consists of the remaining word, the number of deleted pairs before its first edge, and a list of multiplicities at successive vertices after that edge. Consecutive deleted pairs occupy the same insertion slot.", DescribeRole.Definition),
            Node("li-uncu-deletion-insertpeaks", "Insertion at successive vertices", "insertPeaks",
                "Given a word, an initial multiplicity t, and a list of successive multiplicities, insert t up-down pairs before its first edge and continue recursively at later vertices. At the empty word insert only the initial pairs. For a nonempty word and an empty list, insert the initial pairs followed by its first edge.", DescribeRole.Definition),
            Node("li-uncu-deletion-insertible", "Permitted insertion data", "Insertible",
                "The list of multiplicities must have one entry for each edge of the remaining word. Every vertex between an up edge and a following down edge must receive a positive number of inserted pairs. The initial multiplicity has no additional restriction.", DescribeRole.Definition),
            Node("li-uncu-deletion-peakweight", "The peak-abscissa weight", "peakWeight",
                "For a word starting at horizontal coordinate offset, the weight is the sum of horizontal coordinates of vertices between adjacent up and down edges. A deleted up-down pair contributes offset + 1, and scanning then continues two coordinates later.", DescribeRole.Definition),
            Node("li-uncu-deletion-peak-deletion-bijection", "Deletion and insertion are inverse", "peak_deletion_bijection",
                "There is a bijection from all words to triples consisting of a remaining word q, an initial multiplicity t, and a list ts satisfying Insertible. Its forward map is peakData and its inverse is insertPeaks. With N = t + sum(ts), the inserted word has length length(q) + 2N and peak weight N^2 plus the sum of j times the jth entry of ts, with j starting at one.", DescribeRole.Theorem),
            Node("li-uncu-deletion-validpath", "Paths in the bounded strip", "ValidPath",
                "A valid path starts at integer height a, ends at integer height b, and stays between zero and the nonnegative bound H. Up and down edges change height by one. Horizontal edges occur only at height zero. The empty word is valid precisely when a = b and a lies between zero and H.", DescribeRole.Definition),
            Node("li-uncu-deletion-peak-deletion-interior", "Lowering the ceiling at interior endpoints", "peak_deletion_interior",
                "For H at least one, if a valid path has both endpoints strictly below H, deleting all adjacent up-down pairs leaves a valid path with the same endpoints and height bound H - 1.", DescribeRole.Theorem),
            Node("li-uncu-deletion-peak-deletion-ceiling", "Deletion at ceiling endpoints", "peak_deletion_ceiling",
                "For H at least one, a nonempty valid path from H to H has deletion data (down followed by q followed by up, 0, t followed by ts followed by 0). The word q is a valid path from H - 1 to H - 1 with height bound H - 1, and its insertion data t and ts satisfy Insertible.", DescribeRole.Theorem),
            Node("li-uncu-deletion-peak-insertion-valid", "Raising the ceiling by insertion", "peak_insertion_valid",
                "For H at least one, inserting peaks with data satisfying Insertible into a valid path with height bound H - 1 gives a valid path with height bound H and the same endpoints.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}

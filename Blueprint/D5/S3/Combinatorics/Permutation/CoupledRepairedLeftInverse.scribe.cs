using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Permutation;

internal sealed class CoupledRepairedLeftInverseDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Permutation/CoupledRepairedLeftInverse.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/koprowski2026enumeration");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The coupled repaired digit construction has bounded forward digits and recovers both original permutations under the first front and back bounds.",
        H("Left composition of the coupled repaired digit maps"),
        Blocks(
            Paragraph(Text("Permutations use zero-based labels. The original column count is k plus one, the original row count is k plus two, and the first front threshold is L plus one. The parameters satisfy L at most B and B at most k plus one.")),
            Node("cut", "Deletion and standardization", "cut",
                "Delete the entry at the selected position and standardize the surviving labels in increasing order.", DescribeRole.Definition),
            Node("put", "Insertion and lifting", "put",
                "Lift the surviving labels past the inserted label and insert it at the selected position.", DescribeRole.Definition),
            Node("slots", "Low-row positions", "Slots",
                "The low slots are the positions whose permutation values are strictly below the threshold T.", DescribeRole.Definition),
            Node("slot-order", "Increasing enumeration of low slots", "slotOrder",
                "For T at most the permutation size, enumerate its T low slots in increasing position order.", DescribeRole.Definition),
            Node("low-word", "Ordered low subword", "lowWord",
                "Read the permutation values at the increasingly enumerated low slots. This gives a permutation of the labels strictly below T.", DescribeRole.Definition),
            Node("replace", "Replacement in fixed low slots", "replace",
                "Replace the low subword by the supplied permutation while preserving its positions and all high entries.", DescribeRole.Definition),
            Node("actual-algorithms", "The coupled digit maps", "actualAlgorithms",
                "For the forward map, set t to the first column value, delete the row at t and the first column entry, and read the original low subword on labels zero through L. Delete its maximum L and replace the ordinary tail's low subword by the resulting word. The digit d counts the entries after that maximum; b counts the ordinary tail entries before t whose labels are below B. For the inverse map, read the repaired low subword, insert its maximum L at position L minus d, and select t as low slot number b below B. Count the low slots below L before t to identify the deleted label and the original low subword, then undo the row and column deletions.", DescribeRole.Definition),
            Node("actual-full-left-composition", "Recovery of the original pair", "actual_full_left_composition",
                "For all nonnegative integers k, L and B with L at most B and B at most k plus one, let sigma permute the k plus two row labels and pi permute the k plus one column labels. Set t to pi evaluated at zero. Assume sigma at row position t is below L plus one, and sigma at the following row position t plus one is below B plus one. If z is the forward output, its digits satisfy d less than L plus one and b less than B, and applying the inverse to the repaired tail and these digits returns exactly sigma and pi. The B-slot prefix count recovers t. Deletion transports the ordered low slots, and their prefix count recovers the deleted label; these recover the row subword and then both full permutations. The first and last insertion positions, L equal to zero, and k equal to zero are included.", DescribeRole.Theorem),
            Paragraph(Text("This identity concerns the literal permutation maps. The opposite composition, preservation of all board eligibility conditions, the integer weight identity, iteration, and matrix or tensor enumeration require additional results."))
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration,
        string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}

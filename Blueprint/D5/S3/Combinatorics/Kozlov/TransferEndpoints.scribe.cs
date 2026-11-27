using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Kozlov;

internal sealed class TransferEndpointsDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Convexity/snellman2026kozlov");
    private const string Prefix = "D5/S3/Combinatorics/Kozlov/TransferEndpoints.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The two count formulas become first-to-last entries of matrix powers. The endpoint row and column come from the singleton degree and the full simplex.",
        H("The transfer matrices at the first and last states"),
        Blocks(
            Node("firststate", "firstState", "The first transfer state", DescribeRole.Definition,
                "This is state zero of the nonempty state set."),
            Node("laststate", "lastState", "The terminal transfer state", DescribeRole.Definition,
                "This is the state whose zero-based index is n-1."),
            Node("transfer-below", "transfer_below", "Entries below the diagonal vanish", DescribeRole.Theorem,
                "The successor must fill all degrees through the preceding top. Its own top therefore cannot be smaller."),
            Node("transfer-diag", "transfer_diag", "Diagonal entries are one", DescribeRole.Theorem,
                "The successor must fill through its own top and vanish above it. This gives the unique skeleton at that state."),
            Node("transfer-first-row", "transfer_first_row", "The first row gives the initial counts", DescribeRole.Theorem,
                "All carrier vectors already have full degree zero and one, so every state-j vector can follow the first state."),
            Node("transfer-last-column", "transfer_last_column", "The last column is all ones", DescribeRole.Theorem,
                "The full simplex is the unique terminal-state vector and it is an admissible successor from every state."),
            Node("first-vecmul", "first_vecMul", "Selecting the first row by a coordinate vector", DescribeRole.Theorem,
                "Multiplying by the first-state unit row picks the initial row."),
            Node("last-mulvec", "last_mulVec", "Selecting the last column by a coordinate vector", DescribeRole.Theorem,
                "Multiplying by the last-state unit column gives the all-ones column."),
            Node("transfer-sandwich", "transfer_sandwich", "The endpoint matrix power identity", DescribeRole.Theorem,
                "Replace the two boundary vectors by the selected row and column and reassociate multiplication, adding two factors of the transfer matrix."),
            Node("propertransfer", "properTransfer", "The proper transfer matrix", DescribeRole.Definition,
                "Use the actual proper f-vectors as the rank-one carrier. This is the positive-top block of the zero-gap transfer in Part II, Theorem 41."),
            Node("latticetransfer", "latticeTransfer", "The lattice transfer matrix", DescribeRole.Definition,
                "Use the natural rank-one lattice vectors as the carrier. See Part III, equation (42) at zero gap and Lattice/TransferEhrhart.lean, line 444."),
            Node("proper-count-as-entry", "proper_count_as_entry", "The proper count as one matrix entry", DescribeRole.Theorem,
                "The count at rank r+1 equals the first-to-last entry of the proper transfer matrix to power r+2."),
            Node("lattice-count-as-entry", "lattice_count_as_entry", "The lattice count as one matrix entry", DescribeRole.Theorem,
                "The count at rank r+1 equals the first-to-last entry of the lattice transfer matrix to power r+2."),
            Node("propertransfer-unitriangular", "properTransfer_unitriangular", "The proper transfer is upper unitriangular", DescribeRole.Theorem,
                "Proper f-vectors are bounded and fixed, and the full skeleton of each positive cutoff is proper. These facts give the triangular vanishing and diagonal identities. See Part II, Lemma 44."),
            Node("latticetransfer-unitriangular", "latticeTransfer_unitriangular", "The lattice transfer is upper unitriangular", DescribeRole.Theorem,
                "Rank-one lattice vectors are bounded and fixed and contain the full skeleton of each positive cutoff. Apply the same two entry identities to this carrier. See Part III, equation (43) and Lattice/TransferEhrhart.lean, lines 742 and 754."),
            Node("firststate-eq-laststate-iff", "firstState_eq_lastState_iff", "The one-state case", DescribeRole.Theorem,
                "The first index is zero and the last is n-1, which agree exactly when n is one."))));

    private static DocumentBlock Node(string id, string name, string title, DescribeRole role, string prose, Formula? formula = null) =>
        Describe.Lean(DescribeId.Create("kozlov-transfer-endpoints-" + id),
            DeclarationHandle.Create(Prefix + name), H(title),
            formula is null ? StatementSource.WithoutFormula() : StatementSource.FromAuthor(formula),
            name is "properTransfer" or "latticeTransfer" or "properTransfer_unitriangular"
                or "latticeTransfer_unitriangular"
                ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}

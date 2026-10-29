using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class FerrersRowCoordinatesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Partitions/FerrersRowCoordinates.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/FiniteGeometry/barrese2023levels");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Column heights and bottom-to-top row lengths describe the same finite board while retaining every ambient zero.",
        H("Ferrers Coordinates with Ambient Padding"),
        Blocks(
            Node("ferrersrowcoordinates-rows", "Padded row profiles", "Rows",
                "Rows(H,U) consists of all weakly decreasing H-tuples with entries in {0,...,U}. The order is from the bottom row to the top row. The dimensions H and U may be zero.", DescribeRole.Definition),
            Node("ferrersrowcoordinates-board", "Source column heights", "Board",
                "Board(U,H) consists of all weakly increasing U-tuples of heights in {0,...,H}, in the source left-to-right orientation. An entry b_i occupies exactly the cells (i+1,j+1) with 0 <= j < b_i. Zero heights preserve the fixed column slots.", DescribeRole.Definition),
            Node("ferrersrowcoordinates-diagram", "Finite diagram", "diagram",
                "The diagram associated with a row profile has cells (i,j) exactly when i < H and j is less than row i. Its rows use zero-based bottom-to-top coordinates; horizontal reflection converts its left-justified rows into the right-aligned source board. Ambient zero rows remain in Rows even though the finite diagram itself has no cells there.", DescribeRole.Definition),
            Node("ferrersrowcoordinates-conjugate", "Padded conjugation", "conjugate",
                "Conjugation transposes the finite diagram and reads its row lengths in the other fixed ambient dimension. It retains both dimensions, so it also retains the trailing zeros omitted by ordinary partition notation.", DescribeRole.Definition),
            Node("ferrersrowcoordinates-diagram-mem", "Exact finite cells", "diagram_mem",
                "A cell (i,j) belongs to the finite diagram exactly when i is an ambient row index and j is less than that row length. This also describes rows of length zero without deleting their ambient indices.", DescribeRole.Theorem),
            Node("ferrersrowcoordinates-diagram-rowlen", "Recovered row lengths", "diagram_rowLen",
                "At every ambient row index, the finite diagram has exactly the prescribed row length. This is valid with trailing zero rows; no positivity assumption is required.", DescribeRole.Theorem),
            Node("ferrersrowcoordinates-conjugate-involutive", "Conjugation is involutive", "conjugate_involutive",
                "For every nonnegative H and U, conjugating a bounded padded row profile twice gives the original profile, including the zero-dimensional and all-zero cases.", DescribeRole.Theorem),
            Node("ferrersrowcoordinates-boardrowsequiv", "Exact column and row correspondence", "boardRowsEquiv",
                "Reverse the weakly increasing source column tuple, form its Young diagram, and transpose. This is a bijection from Board(U,H) to Rows(H,U); the inverse conjugates and reverses. This fixes the source right alignment and does not identify different ambient column slots.", DescribeRole.Definition),
            Node("ferrersrowcoordinates-board-row-count", "The row coordinate counts actual cells", "board_row_count",
                "For every source board and each ambient row i, the row coordinate equals the number of column indices j whose height exceeds i. Thus the coordinate bijection preserves the number of literal cells in every row, and consequently in each consecutive block of rows.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}

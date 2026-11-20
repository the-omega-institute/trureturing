using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class NiuQ15TableauxDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Partitions/NiuQ15Tableaux.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/PermutationPatterns/niu2026firstdescent");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Maximum-cell deletion for straight tableaux and prefix rotation for rectangular tableaux.",
        H("Deletion and Rotation of Standard Tableaux"),
        Blocks(
            Node("niuq15tableaux-rowshape", "Straight shapes", "RowShape",
                "The row lengths are a weakly decreasing function on a finite set of row indices. A cell consists of a row index and a column index strictly below that row's length.",
                DescribeRole.Definition),
            Node("niuq15tableaux-standardtableau", "Standard tableaux", "StandardTableau",
                "A standard tableau is a strictly increasing bijection from the cells in product order to the labels from zero through the number of cells minus one. Adding one to each label gives the paper's entry convention.",
                DescribeRole.Definition),
            Node("niuq15tableaux-strictmono-iff-rows-columns", "Row and column increase", "strictMono_iff_rows_columns",
                "Strict monotonicity of a cell labeling is equivalent to strict increase along every row and every column.",
                DescribeRole.Theorem),
            Node("niuq15tableaux-removable-iff-next", "Removable rows", "removable_iff_next",
                "A row is removable exactly when it is nonempty and the next row, if present, has strictly smaller length. The last row needs only positive length.",
                DescribeRole.Theorem),
            Node("niuq15tableaux-standardtableaudeletelast", "Delete the maximum label", "standardTableauDeleteLast",
                "For a nonempty shape, delete the cell carrying the largest label. Its row is removable. Inserting the largest label at the end of that row inverts the construction.",
                DescribeRole.Definition),
            Node("niuq15tableaux-card-standardtableau-eq-sum", "Cardinality recurrence", "card_standardTableau_eq_sum",
                "The tableau count of a nonempty shape is the sum of the counts obtained by deleting the last cell of each removable row.",
                DescribeRole.Theorem),
            Node("niuq15tableaux-card-standardtableau-of-size-zero", "Empty tableau", "card_standardTableau_of_size_zero",
                "For any row shape of total size zero, the standard tableau count is one.",
                DescribeRole.Theorem),
            Node("niuq15tableaux-firstdescent", "First descent", "firstDescent",
                "For a positive-width rectangle with at least two rows, the statistic is the entry at row two and column one minus one.",
                DescribeRole.Definition, true),
            Node("niuq15tableaux-firstdescent-isleast", "Least descent", "firstDescent_isLeast",
                "With positions indexed by the one-based entries, the statistic is the least index whose successor lies in a strictly lower row.",
                DescribeRole.Theorem),
            Node("niuq15tableaux-rotatedshape", "Shortened rectangle", "rotatedShape",
                "After removing a prefix of length r from the top row and rotating, all rows retain their width except the bottom row, whose length decreases by r.",
                DescribeRole.Definition),
            Node("niuq15tableaux-rectangletailrotation", "Rotate the first-descent survival event", "rectangleTailRotation",
                "For a positive-width rectangle with at least two rows and zero through width as the threshold, tableaux with first descent at least the threshold are in bijection with standard tableaux of the shortened shape. The map deletes the prescribed top-row prefix, rotates the remaining cells by 180 degrees and complements their labels.",
                DescribeRole.Definition)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, bool literature = false) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}

using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class NiuTableauCountDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Partitions/NiuTableauCount.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The rational shifted-node formula obeys the same deletion recurrence as the number of standard tableaux of a straight shape.",
        H("Row Deletion for the Shifted Vandermonde Formula"),
        Blocks(
            Node("niu-tableau-delete-row", "Delete a cell", "deleteRow",
                "Subtract one, with natural-number truncation, from the selected row length and retain all k row slots.",
                DescribeRole.Definition),
            Node("niu-tableau-removable-row", "Removable rows", "RemovableRow",
                "A row is removable when its length is positive and strictly greater than the length of every later row.",
                DescribeRole.Definition),
            Node("niu-tableau-shifted-node", "Shifted row length", "shiftedNode",
                "Add the number of row slots below a row to its length.",
                DescribeRole.Definition),
            Node("niu-tableau-vandermonde", "Vandermonde product", "vandermonde",
                "Multiply the differences b_i - b_j for all pairs of row indices i < j.",
                DescribeRole.Definition),
            Node("niu-tableau-shifted-count", "Shifted-node formula", "shiftedCount",
                "For row lengths lambda indexed from zero, set b_i = lambda_i + k - 1 - i and let N be the sum of the row lengths. The formula is N! times the product of b_i - b_j over i < j, divided by the product of b_i! over all rows, in the rational numbers.",
                DescribeRole.Definition),
            Node("niu-tableau-empty-count", "Empty diagram", "shiftedCount_empty",
                "For every k, the empty profile has value one. For fixed i the differences b_i - b_j with j > i run through 1 up to b_i, so their product cancels b_i!.",
                DescribeRole.Theorem),
            Node("niu-tableau-count-recurrence", "One-cell deletion recurrence", "shiftedCount_recurrence",
                "For k at least two and weakly decreasing row lengths of positive total size, the formula is the sum of its values after deleting one cell from each removable row. The factors of the Vandermonde product involving that row give its deletion weight. A nonremovable row has weight zero. Polynomial interpolation shows that the sum of all weights is N, which cancels the ratio N! / (N - 1)!.",
                DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}

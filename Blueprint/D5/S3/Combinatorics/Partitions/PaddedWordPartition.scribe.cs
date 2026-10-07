using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class PaddedWordPartitionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Partitions/PaddedWordPartition.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The reverse list of horizontal prefix counts at vertical letters is a padded decreasing partition. Its row and conjugate column squares determine the two centered moments of the same word at its direct area count.",
        H("Direct prefix partitions and their two fan moments"),
        Blocks(
            Node("prefix-rows", "Zero-padded reverse prefix rows", "rows", DescribeRole.Definition,
                "At every false letter, record the number of preceding true letters, then reverse the recorded list. The list contains one entry for every false letter, including zero entries. Its sum is the scattered true-before-false count and each row is bounded by the total true count."),
            Node("actual-diagram", "The actual Young diagram", "diagram", DescribeRole.Definition,
                "The decreasing padded list defines a Young diagram by its cells. Zero entries stay in the padded list even though they contribute no cells. The row statistic is the sum of the row squares. The column statistic sums the squares of the rows of this very diagram's transpose, padded to the true count."),
            Node("same-columns", "Column squares from the same cells", "same_diagram_columns", DescribeRole.Theorem,
                "A column of height h has square equal to the sum of the first h odd positive integers. Summing over columns and interchanging the finite cell sums gives the odd-position weighted sum of the original rows. The equality uses membership in one diagram and its actual transpose."),
            Node("direct-fan", "All words at direct area", "all_word_direct", DescribeRole.Theorem,
                "For every binary word, with u true letters, v false letters, K scattered true-before-false pairs, row-square sum P and transposed column-square sum R, the exact coordinates are D = 2K - uv, E = u squared times v - 6uK + 6P, and F = minus u times v squared + 6vK - 6R. K is used directly, including values above half the rectangle area. Empty auxiliary words, pure-letter words and zero signed area need no additional hypothesis or division. Actual acquisition, common calibration and exact arithmetic remain independent premises when the formula is used for a physical source.")),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        DescribeRole role, string prose) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}

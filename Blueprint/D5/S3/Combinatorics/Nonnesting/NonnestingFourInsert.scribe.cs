using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Nonnesting;

internal sealed class NonnestingFourInsertDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Nonnesting/NonnestingFourInsert.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/elizalde2024pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two initial arrangements preserve four-pattern avoidance and first order.",
        H("Insertion into Increasing-Order Avoiders"),
        Blocks(
            Node("nonnesting-nonnestingfourinsert-crossing-insert", "Crossing insertion preserves avoidance", "crossing_insert",
                "If a word begins with one and avoids the four patterns, prepending 121 after shifting its tail yields an avoider of size one greater.", DescribeRole.Theorem),
            Node("nonnesting-nonnestingfourinsert-crossing-insert-first-order", "First order after crossing insertion", "crossing_insert_first_order",
                "The 121 insertion preserves increasing order of first occurrences.", DescribeRole.Theorem),
            Node("nonnesting-nonnestingfourinsert-cut-insert-first-order", "First order after cut insertion", "cut_insert_first_order",
                "Prepending 11 to a shifted word preserves increasing order of first occurrences.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}

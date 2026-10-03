using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Nonnesting;

internal sealed class NonnestingBasicDeletionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Nonnesting/NonnestingBasicDeletion.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/elizalde2024pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Deleting the smallest doubled letter preserves avoidance and first order.",
        H("Deletion of the Least Value"),
        Blocks(
            Node("nonnesting-nonnestingbasicdeletion-delete-lowest-avoider", "Deleting both ones preserves avoidance", "delete_lowest_avoider",
                "Removing both copies of one and decrementing the remaining letters sends an avoider of size n plus one to an avoider of size n.", DescribeRole.Theorem),
            Node("nonnesting-nonnestingbasicdeletion-first-order-after-filter", "First order survives filtering", "first_order_after_filter",
                "Filtering a word above k preserves the order of first occurrences of any two retained letters.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}

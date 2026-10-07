using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PatternMatchings;

internal sealed class P13OrdersDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PatternMatchings/P13Orders.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/PermutationPatterns/biswas2026matchingtriples");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One common closing-time function realizes every comparison imposed by an accepted normalized scan.",
        H("Transporting total orders through queue deletion"),
        Blocks(
            Node("p13-p13orders-respects", "Old base constraints", "Respects",
                "A closing-time function respects all comparisons among old survivors in the normalized base; it imposes no comparison on pending openings.", DescribeRole.Definition),
            Node("p13-p13orders-closurerespects", "The order imposed by one closure", "ClosureRespects",
                "Every two surviving queue entries close in the order prescribed by the two blocks on opposite sides of the selected rank.", DescribeRole.Definition),
            Node("p13-p13orders-closure-comparison", "Every comparison is determined", "closure_comparison",
                "A closing-time function respecting the full imposed survivor order compares any two survivor times exactly according to that order, in both directions.", DescribeRole.Theorem),
            Node("p13-p13orders-deletion-order", "Order transport across actual queue deletion", "deletion_order",
                "For an in-range closing rank, realization of the new normalized base on the queue after deletion is equivalent to realization of the full imposed order on the original survivors.", DescribeRole.Theorem),
            Node("p13-p13orders-compatible-of-orders", "Necessity of all old constraints", "compatible_of_orders",
                "If the same closing-time function realizes the old base, the new closure order and the current selected opener as the first closure, then all old comparisons are compatible with the new order.", DescribeRole.Theorem),
            Node("p13-p13orders-respects-of-compatible", "Sufficiency for all old constraints", "respects_of_compatible",
                "Compatibility, the realized new survivor order and the selected opener as the first closure together imply every comparison of the old base, including those involving the opener just removed.", DescribeRole.Theorem),
            Node("p13-p13orders-orderedrun", "All orders of a complete scan", "OrderedRun",
                "At each closure the survivor closing times realize the imposed total two-block order; openings add no comparison.", DescribeRole.Definition),
            Node("p13-p13orders-normalized-run", "Exhaustive arbitrary-size normalization", "normalized_run",
                "For any actual matching realizing an ordered scan, local acceptance from a valid old base and a separate pending count is equivalent to realization of the old base and every subsequently imposed closure order. Each induction step uses the same actual closing times, so earlier constraints remain compatible throughout the scan.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}

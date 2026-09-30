using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class ArrowThirtyTwoOneThreeRefinedDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/ArrowThirtyTwoOneThreeRefined.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/zhou2026arrow");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The final-cycle bijection yields a Catalan-weighted recurrence for the avoidance numbers.",
        H("Refined Counts by Final Cycle"),
        Blocks(
            Node("arrow-thirty-two-cycle-word-count", "Catalan orders ending at the maximum", "final_cycle_word_count",
                "For a finite set t below b, the orders of t together with b that end in b and avoid 132 are counted by the Catalan number of the size of t.", DescribeRole.Theorem),
            Node("arrow-thirty-two-stratum-card", "A positive final-cycle stratum", "stratum_card_positive",
                "For k plus one at most n, the number of avoiders of size n plus one with k plus one letters after n plus one is the kth Catalan number times the coefficient of x to the n minus k minus one in the (k plus two)nd power of the avoidance series.", DescribeRole.Theorem),
            Node("arrow-thirty-two-recurrence", "Recurrence for all avoidance numbers", "count_recurrence",
                "For every positive n, the count at n equals the count at n minus one plus the sum over k from one through n minus one of the (k minus one)st Catalan number times the coefficient of x to the n minus one minus k in the (k plus one)st power of the avoidance series.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}

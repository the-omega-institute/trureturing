using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class ArrowThirtyTwoOneThreeBijectionGapsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/ArrowThirtyTwoOneThreeBijectionGaps.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/zhou2026arrow");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The edge condition respects increasing relabelling and cuts at missing values.",
        H("Value Gaps and Closed Edges"),
        Blocks(
            Node("arrow-thirty-two-closed-edges", "Closed ascending edges", "ClosedEdges",
                "A word has closed edges when every value strictly between an entry and a larger inverse Foata successor appears before that successor in the word.", DescribeRole.Definition),
            Node("arrow-thirty-two-monotone-hat", "Increasing relabelling of successors", "hat_map_strictMono",
                "For an entry belonging to a word, a strictly increasing relabelling carries its inverse Foata successor to the successor of its relabelled entry.", DescribeRole.Theorem),
            Node("arrow-thirty-two-translate-edges", "Translation of closed edges", "closedEdges_translate",
                "Adding the same nonnegative integer to every letter preserves and reflects the closed-edge condition.", DescribeRole.Theorem),
            Node("arrow-thirty-two-ordered-hat", "Successors in ordered concatenations", "hat_append_ordered",
                "When every letter of L is smaller than every letter of R, the inverse Foata successor of each letter in L or R agrees with its successor within that part.", DescribeRole.Theorem),
            Node("arrow-thirty-two-ordered-edges", "Closed edges in ordered concatenations", "closedEdges_append_ordered",
                "When all letters of L are below all letters of R, their concatenation has closed edges exactly when each part has closed edges.", DescribeRole.Theorem),
            Node("arrow-thirty-two-value-cut", "Cutting at a missing value", "closedEdges_value_cut",
                "A word with distinct letters and closed edges, omitting c, consists first of all its letters below c and then all its letters above c.", DescribeRole.Theorem),
            Node("arrow-thirty-two-cycle-confinement", "Cycles cannot cross a missing value", "closedEdges_cycle_confinement",
                "In a word with distinct letters and closed edges that omits c, every iterate of the inverse Foata successor of an entry remains in the word and stays on the same side of c as that entry.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}

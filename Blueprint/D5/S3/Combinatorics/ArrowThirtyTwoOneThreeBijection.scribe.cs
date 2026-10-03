using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class ArrowThirtyTwoOneThreeBijectionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/ArrowThirtyTwoOneThreeBijection.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/zhou2026arrow");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The prefix and final cycle of an avoider satisfy complementary edge and pattern conditions.",
        H("Reconstructing the Final Cycle"),
        Blocks(
            Node("arrow-thirty-two-final-hat", "Prefix successors before the final cycle", "hat_append_final_cycle",
                "If m exceeds every entry of q, placing m and a following word after q leaves every inverse Foata successor of an entry of q unchanged.", DescribeRole.Theorem),
            Node("arrow-thirty-two-no-cross", "No prefix edge crosses a final-cycle letter", "no_prefix_edge_crosses_final_cycle",
                "For an avoider split before its largest value, a final-cycle letter c above a prefix letter a cannot lie below the inverse Foata successor of a in the prefix.", DescribeRole.Theorem),
            Node("arrow-thirty-two-prefix-condition", "The prefix inherits the edge condition", "prefix_edge_condition_of_avoider",
                "Every ascending inverse Foata edge in the prefix of an avoider has all intermediate values before its endpoint within that prefix.", DescribeRole.Theorem),
            Node("arrow-thirty-two-final-edge", "Edges of a permissible final cycle", "final_cycle_edge_condition",
                "Suppose the whole word is a permutation, the final-cycle word ends in its largest letter b, and it avoids 132. Then each edge starting in that word satisfies the avoidance edge condition.", DescribeRole.Theorem),
            Node("arrow-thirty-two-append-largest-132", "Appending a largest letter preserves 132", "has132_append_max_iff",
                "If b exceeds every entry of u, the word u followed by b contains 132 exactly when u does.", DescribeRole.Theorem),
            Node("arrow-thirty-two-final-characterization", "Necessary final-cycle conditions", "final_cycle_strict_max_and_avoid132",
                "In an avoider whose last cycle is n plus one followed by u and b, b strictly exceeds every letter of u, and u avoids 132.", DescribeRole.Theorem),
            Node("arrow-thirty-two-singleton-card", "Counting singleton final cycles", "singleton_final_cycle_count",
                "The avoiders of size n plus one ending in n plus one are counted by the avoidance number at n.", DescribeRole.Theorem),
            Node("arrow-thirty-two-construct", "Constructing an avoider", "construct_avoider_of_local_conditions",
                "A permutation formed from a prefix q and final cycle beginning with n plus one is an avoider when prefix edges are closed, no prefix edge crosses a final-cycle letter, and the final-cycle word ends in its largest letter after a 132-avoiding initial part.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}

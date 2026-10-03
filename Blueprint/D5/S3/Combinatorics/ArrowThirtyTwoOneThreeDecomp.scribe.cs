using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class ArrowThirtyTwoOneThreeDecompDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/ArrowThirtyTwoOneThreeDecomp.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/zhou2026arrow");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The largest value begins the final cycle, whose entries have a constrained order.",
        H("Splitting at the Largest Value"),
        Blocks(
            Node("arrow-thirty-two-append-fresh", "Appending a new maximum", "hat_append_fresh_max",
                "If m exceeds every entry of q, appending m leaves the inverse Foata successor of each entry of q unchanged.", DescribeRole.Theorem),
            Node("arrow-thirty-two-last-wrap", "The last edge returns to the maximum", "hat_last_entry_eq_max",
                "In a permutation of 1 through n plus one, the inverse Foata successor of its last entry is n plus one.", DescribeRole.Theorem),
            Node("arrow-thirty-two-next-after-max", "Successors after the maximum", "hat_next_after_max",
                "For any entry after n plus one that has a following entry, the inverse Foata successor is that following entry.", DescribeRole.Theorem),
            Node("arrow-thirty-two-singleton-iff", "A singleton final cycle", "append_max_avoiders_iff",
                "Appending the new maximum n plus one to q produces an avoider exactly when q is an avoider on 1 through n.", DescribeRole.Theorem),
            Node("arrow-thirty-two-final-max", "The last letter is largest", "final_cycle_last_is_max",
                "If an avoider ends in a final cycle beginning with n plus one and ending in a, every preceding letter of that cycle is at most a.", DescribeRole.Theorem),
            Node("arrow-thirty-two-final-132", "The final-cycle tail avoids 132", "final_cycle_avoid132",
                "The word following the largest value in the final cycle of an avoider contains no classical 132 pattern.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}

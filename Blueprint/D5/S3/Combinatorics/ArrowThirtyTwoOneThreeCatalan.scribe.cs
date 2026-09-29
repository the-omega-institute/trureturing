using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class ArrowThirtyTwoOneThreeCatalanDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/ArrowThirtyTwoOneThreeCatalan.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/zhou2026arrow");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The final-cycle orders are counted by Catalan numbers through classical 132-avoidance.",
        H("Catalan Orders of the Final Cycle"),
        Blocks(
            Node("arrow-thirty-two-has-132", "Classical 132 occurrence", "Has132",
                "A word contains 132 when entries at positions i less than j less than k have values at i less than the value at k, which is less than the value at j.", DescribeRole.Definition),
            Node("arrow-thirty-two-has-adj-132", "Adjacent 13-2 occurrence", "HasAdj132",
                "A word contains 13-2 when the first two entries of such a triple are adjacent, while the third occurs later.", DescribeRole.Definition),
            Node("arrow-thirty-two-adj-iff", "Adjacent and classical patterns coincide", "hasAdj132_iff",
                "For a word with distinct entries, a 13-2 occurrence exists exactly when a classical 132 occurrence exists.", DescribeRole.Theorem),
            Node("arrow-thirty-two-split-132", "Avoidance across a maximum", "avoids132_append_max_iff",
                "When m exceeds every entry of L and R, their concatenation around m avoids 132 exactly when both parts avoid 132 and every entry of L is at least every entry of R.", DescribeRole.Theorem),
            Node("arrow-thirty-two-upper-unique", "Uniqueness of upper parts", "upper_parts_unique",
                "Two upper-closed subsets of the same finite ordered set are equal when they have the same cardinality.", DescribeRole.Theorem),
            Node("arrow-thirty-two-upper-exists", "Upper parts of every size", "exists_upper_part",
                "Every size from zero through the cardinality of a finite ordered set occurs as the cardinality of an upper-closed subset.", DescribeRole.Theorem),
            Node("arrow-thirty-two-catalan-card", "Counting 132-avoiding orders", "ncard_avoid132",
                "The number of 132-avoiding orders of any finite set of natural numbers is the Catalan number indexed by its cardinality.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}

using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.VincularStack;

internal sealed class VincularStackThreeBasicDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/VincularStack/VincularStackThreeBasic.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Words/zhao2024vincular");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Adjacent pattern occurrences and order preservation control the three stack maps.",
        H("Pattern Occurrences and Stack Invariants"),
        Blocks(
            Node("vincularstack-vincularstackthreebasic-classical-adjacent", "An adjacent descent in a 312 occurrence", "classical_adjacent",
                "A word with distinct entries contains the classical pattern 312 if and only if it contains 31-2 with the entries playing 3 and 1 adjacent.", DescribeRole.Theorem),
            Node("vincularstack-vincularstackthreebasic-push-preserves", "Preservation under insertion", "push_preserves",
                "For any pair of adjacency flags, if the initial stack avoids the specified form of 312, right-greedy insertion leaves a stack avoiding that form. The concatenation of the popped entries and the remaining stack is a permutation of the inserted entry followed by the original stack, and contains the original stack as a subsequence.", DescribeRole.Theorem),
            Node("vincularstack-vincularstackthreebasic-process-preserves", "Preservation under processing", "process_preserves",
                "For any pair of adjacency flags, processing any input from a stack avoiding the specified form of 312 produces a permutation of the input concatenated with that stack. The original stack occurs as a subsequence of the output.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}

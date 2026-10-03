using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.VincularStack;

internal sealed class VincularStackBasicDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/VincularStack/VincularStackBasic.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Words/zhao2024vincular");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Stack invariants determine the output position of a newly inserted maximum.",
        H("Stack Invariants and Maximum Insertion"),
        Blocks(
            Node("vincularstack-vincularstackbasic-push-test", "Testing a proposed push", "push_test",
                "Placing an entry before a stack with top t creates a 23-1 occurrence precisely when the original stack already contains 23-1, or the entry is less than t and some entry below t is less than the inserted entry.", DescribeRole.Theorem),
            Node("vincularstack-vincularstackbasic-push-preserves", "Preservation under insertion", "push_preserves",
                "If the initial stack avoids 23-1, right-greedy insertion leaves a stack avoiding 23-1. The concatenation of the popped entries and the remaining stack is a permutation of the inserted entry followed by the original stack, and contains the original stack as a subsequence.", DescribeRole.Theorem),
            Node("vincularstack-vincularstackbasic-push-minimum", "Retention of a minimum", "push_minimum",
                "Suppose the stack avoids 23-1 and contains a minimum m, and the inserted entry is at least m. Then m remains in the stack after insertion, and every popped entry is strictly greater than m.", DescribeRole.Theorem),
            Node("vincularstack-vincularstackbasic-process-preserves", "Preservation under processing", "process_preserves",
                "Processing any input from a stack avoiding 23-1 produces a permutation of the input concatenated with that stack. The original stack occurs as a subsequence of the output.", DescribeRole.Theorem),
            Node("vincularstack-vincularstackbasic-snapshot", "The state before the final drain", "snapshot",
                "A snapshot records the output already popped and the stack remaining after all input entries have been inserted, before draining the final stack.", DescribeRole.Definition),
            Node("vincularstack-vincularstackbasic-snapshot-minimum", "A minimum in the final stack", "snapshot_minimum",
                "Suppose the initial stack avoids 23-1 and m is a minimum of the input concatenated with the stack. The snapshot stack avoids 23-1 and contains m, every entry already popped is strictly greater than m, and the full output is the popped word concatenated with the snapshot stack.", DescribeRole.Theorem),
            Node("vincularstack-vincularstackbasic-protected-suffix", "A protected bottom segment", "protected_suffix",
                "Suppose a stack avoiding 23-1 is an upper segment followed by a bottom segment. If the upper segment contains m and every entry in both segments is at least m, processing any input leaves the bottom segment untouched: the full output equals the output from the upper segment alone followed by the bottom segment.", DescribeRole.Theorem),
            Node("vincularstack-vincularstackbasic-outputgap", "The output gap of a maximum", "outputGap",
                "Split an input into a front and a suffix. If the front is empty, its output gap is the suffix length. Otherwise take the snapshot of the front from an empty stack. If the suffix is empty, or the snapshot stack contains an entry less than the first suffix entry, the gap is the popped length. In the remaining case it is the total input length minus the snapshot stack length.", DescribeRole.Definition),
            Node("vincularstack-vincularstackbasic-maximum-insertion", "Inserting a maximum in the output", "maximum_insertion",
                "Let M exceed every entry of a front concatenated with a suffix. Inserting M between those two words inserts M into their original SC output at the output gap of that split and leaves the other entries in their original order. If the front is nonempty, the gap is strictly less than the original input length.", DescribeRole.Theorem),
            Node("vincularstack-vincularstackbasic-separatingcut", "Separating output cuts", "separatingCut",
                "A gap in a word is a separating cut when every entry before the gap is strictly less than every entry at or after the gap.", DescribeRole.Definition),
            Node("vincularstack-vincularstackbasic-maximum-cut", "Avoidance after inserting a maximum", "maximum_cut",
                "Let a front concatenated with a back have distinct entries, all less than M. The word obtained by inserting M between them avoids 231 precisely when the original word avoids 231 and the cut between the front and back is separating.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}

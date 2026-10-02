using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.VincularStack;

internal sealed class VincularStackThreeDefsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/VincularStack/VincularStackThreeDefs.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Words/zhao2024vincular");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The stacks avoiding 312, 31-2 and 3-12 define three sorting classes and their common-output assertion.",
        H("Three Stacks Avoiding Patterns of Order Three"),
        Blocks(
            Node("vincularstack-vincularstackthreedefs-contains312", "The three forms of 312", "Contains312",
                "A stack word, read from top to bottom, contains 312 when three entries at strictly increasing positions have the second entry less than the third and the third less than the first. The flag adj31 requires the first two positions to be adjacent, giving 31-2; the flag adj12 requires the last two positions to be adjacent, giving 3-12. When both flags are false, there is no adjacency requirement.", DescribeRole.Definition),
            Node("vincularstack-vincularstackthreedefs-decidable-contains312", "Decidable pattern containment", "instDecidableContains312",
                "Containment of each specified form of 312 in a finite stack word is decidable by testing all bounded triples of positions, their value inequalities and the required adjacencies.", DescribeRole.Definition),
            Node("vincularstack-vincularstackthreedefs-push", "Right-greedy insertion", "Push",
                "To insert an entry, push it onto the stack if the resulting stack avoids the specified form of 312. Otherwise pop the top entry and retry. The operation returns the popped entries in their output order and the remaining stack, read from top to bottom.", DescribeRole.Definition),
            Node("vincularstack-vincularstackthreedefs-process", "Processing a word", "Process",
                "Starting from a given stack, process the input word from left to right by right-greedy insertion. Concatenate the popped entries in order and then the final stack read from top to bottom.", DescribeRole.Definition),
            Node("vincularstack-vincularstackthreedefs-sc", "The three stack maps", "SC",
                "The map SC sends a word to the output obtained by processing it from an empty stack. The flag pairs false and false, true and false, and false and true specify avoidance of 312, 31-2 with the entries playing 3 and 1 adjacent, and 3-12 with the entries playing 1 and 2 adjacent, respectively.", DescribeRole.Definition),
            Node("vincularstack-vincularstackthreedefs-sortable", "The sorting classes", "sortable",
                "For every nonnegative n and each pair of adjacency flags, the sorting class consists of permutations of the integers from one through n whose image under the corresponding stack map avoids the classical pattern 231.", DescribeRole.Definition),
            Node("vincularstack-vincularstackthreedefs-claim", "Equal sorting classes and common outputs", "claim",
                "For every positive n, the sorting classes of the stacks avoiding 312, 31-2 with the entries playing 3 and 1 adjacent, and 3-12 with the entries playing 1 and 2 adjacent are equal. On every permutation in the common sorting class, the three stack maps have equal outputs.", DescribeRole.Definition)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}

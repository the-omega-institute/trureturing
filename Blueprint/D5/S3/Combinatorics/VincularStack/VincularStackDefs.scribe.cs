using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.VincularStack;

internal sealed class VincularStackDefsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/VincularStack/VincularStackDefs.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Words/zhao2024vincular");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The right-greedy stack avoiding 23-1 defines a sorting class and its Schroeder enumeration assertion.",
        H("The Stack Avoiding 23-1"),
        Blocks(
            Node("vincularstack-vincularstackdefs-containsv", "The vincular pattern 23-1", "ContainsV",
                "A stack word, read from top to bottom, contains 23-1 when two adjacent entries are increasing and a later entry is less than the first of those two entries.", DescribeRole.Definition),
            Node("vincularstack-vincularstackdefs-decidable-containsv", "Decidable pattern containment", "instDecidableContainsV",
                "Containment of 23-1 in a finite stack word is decidable by testing all bounded choices of the adjacent positions and the later position.", DescribeRole.Definition),
            Node("vincularstack-vincularstackdefs-push", "Right-greedy insertion", "Push",
                "To insert an entry, push it onto the stack if the resulting stack avoids 23-1. Otherwise pop the top entry and retry. The operation returns the popped entries in their output order and the remaining stack, read from top to bottom.", DescribeRole.Definition),
            Node("vincularstack-vincularstackdefs-process", "Processing a word", "Process",
                "Starting from a given stack, process the input word from left to right by right-greedy insertion. Concatenate the popped entries in order and then the final stack read from top to bottom.", DescribeRole.Definition),
            Node("vincularstack-vincularstackdefs-sc", "The right-greedy stack map", "SC",
                "The map SC sends a word to the output obtained by processing it from an empty stack with right-greedy insertion avoiding 23-1.", DescribeRole.Definition),
            Node("vincularstack-vincularstackdefs-contains231", "The classical pattern 231", "Contains231",
                "A word contains 231 when three entries at strictly increasing positions have the third entry less than the first and the first less than the second.", DescribeRole.Definition),
            Node("vincularstack-vincularstackdefs-sortable", "The sorting class", "sortable",
                "For every nonnegative n, the sorting class consists of permutations of the integers from one through n whose image under SC avoids the classical pattern 231.", DescribeRole.Definition),
            Node("vincularstack-vincularstackdefs-claim", "The Schroeder enumeration assertion", "claim",
                "For every positive n, the number of permutations of one through n whose image under SC avoids 231 equals the large Schroeder number of index n minus one.", DescribeRole.Definition)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}

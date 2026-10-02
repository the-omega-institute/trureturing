using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PopStack;

internal sealed class PopStackDefsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PopStack/PopStackDefs.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/cioni2025sorting");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The assertion is that the numbers of simple permutations in C of sizes zero, one and two are respectively one, one and two, and that for every n at least three the number is F_(2n-5) minus the remainder of n on division by two. The Fibonacci sequence has F_0 = 0 and F_1 = 1.",
        H("The Fibonacci enumeration assertion"),
        Blocks(
            Node("pop-stack-popstackdefs-occurs", "Classical pattern containment", "Occurs",
                "A pattern occurs in a word when a subsequence of that word has the same relative order as the pattern.", DescribeRole.Definition),
            Node("pop-stack-popstackdefs-basis", "The forbidden basis", "basis",
                "The forbidden basis consists of 2341, 25314, 42513, 42531, 45213, 45231, 52314, 642135 and 642153.", DescribeRole.Definition),
            Node("pop-stack-popstackdefs-inc", "The sortable class", "InC",
                "A word belongs to C when none of the patterns in the forbidden basis occurs in it.", DescribeRole.Definition),
            Node("pop-stack-popstackdefs-issimple", "Simple permutations", "IsSimple",
                "A word is simple when no consecutive segment of length at least two and less than its total length has a set of consecutive values.", DescribeRole.Definition),
            Node("pop-stack-popstackdefs-simples", "Simple sortable permutations of a fixed size", "simples",
                "For each nonnegative n, simples(n) is the set of permutations of the integers from one through n that belong to C and are simple.", DescribeRole.Definition),
            Node("pop-stack-popstackdefs-claim", "The Fibonacci enumeration assertion", "claim",
                "The assertion is that the numbers of simple permutations in C of sizes zero, one and two are respectively one, one and two, and that for every n at least three the number is F_(2n-5) minus the remainder of n on division by two. The Fibonacci sequence has F_0 = 0 and F_1 = 1.", DescribeRole.Definition)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}

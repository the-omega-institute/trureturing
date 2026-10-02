using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PopStack;

internal sealed class PopStackTerminalIntervalsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PopStack/PopStackTerminalIntervals.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/cioni2025sorting");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For n at least four, R(n) is a permutation of size n in C ending in its minimum. Its proper nontrivial intervals are exactly the prefix of length n minus one with values from two through n and, when n is even, the second and third entries with values n minus one and n. Moreover, Y(n+1) is a simple permutation of size n + 1 in C.",
        H("Intervals and simplicity in the terminal families"),
        Blocks(
            Node("pop-stack-popstackterminalintervals-y", "Minimum insertion in the terminal-gap family", "Y",
                "For each nonnegative n, Y(n) is obtained from R(n-1) by increasing every entry by one and inserting the minimum one at zero-based position two. Subtraction is truncated at zero.", DescribeRole.Definition),
            Node("pop-stack-popstackterminalintervals-terminal-family-intervals", "Intervals and simplicity in the terminal families", "terminal_family_intervals",
                "For n at least four, R(n) is a permutation of size n in C ending in its minimum. Its proper nontrivial intervals are exactly the prefix of length n minus one with values from two through n and, when n is even, the second and third entries with values n minus one and n. Moreover, Y(n+1) is a simple permutation of size n + 1 in C.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}

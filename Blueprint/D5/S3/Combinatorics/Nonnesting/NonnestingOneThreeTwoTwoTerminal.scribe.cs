using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Nonnesting;

internal sealed class NonnestingOneThreeTwoTwoTerminalDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwoTerminal.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/elizalde2024pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The last first occurrence determines a unique terminal insertion of one of two types.",
        H("Unique Terminal Factorization"),
        Blocks(
            Node("nonnesting-nonnestingonethreetwotwoterminal-terminal-factorization", "Two-type terminal factorization", "terminal_factorization",
                "Let a word have exactly two copies of each of its letters, and let the pivot have the last first occurrence. The word avoids 1221, 2112, and 1322 if and only if its upper and lower subsequences avoid all three patterns and it has unique type I or type II parameters. In type I, the cut is at most the lower length and follows every lower first occurrence. In type II, the lower subsequence consists of two copies of an order with distinct entries, and the cut is strictly below the upper length and follows every upper first occurrence. The length after the first pivot is lower length minus cut plus one in type I, and upper length minus cut plus lower order length plus one in type II.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}

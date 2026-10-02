using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PopStack;

internal sealed class PopStackTerminalGapDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PopStack/PopStackTerminalGap.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/cioni2025sorting");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Let p be a permutation of size n at least four in D ending with its minimum. Suppose every proper nontrivial interval crosses the gap of zero-based index two strictly and has minimum value at least two. Then p = R(n).",
        H("Classification of a terminal crossing gap"),
        Blocks(
            Node("pop-stack-popstackterminalgap-r", "The terminal-gap family", "R",
                "For odd n, R(n) equals E(floor(n/2)). For even n, its first two entries are n/2 and n; at later even zero-based position i its entry is n minus i/2, and at later odd position i its entry is n/2 minus floor(i/2).", DescribeRole.Definition),
            Node("pop-stack-popstackterminalgap-terminal-gap-classification", "Classification of a terminal crossing gap", "terminal_gap_classification",
                "Let p be a permutation of size n at least four in D ending with its minimum. Suppose every proper nontrivial interval crosses the gap of zero-based index two strictly and has minimum value at least two. Then p = R(n).", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}

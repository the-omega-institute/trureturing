using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PopStack;

internal sealed class PopStackMaximumTerminalDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PopStack/PopStackMaximumTerminal.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/cioni2025sorting");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Let p have size n at least four and maximum second. Assume the upper values after its first two entries decrease, no lower value has both a smaller and a larger lower value later, and adjacent values are never consecutive, where upper and lower are relative to its first entry. If the minimum has even zero-based position k at least two and the first entry equals k/2 + 1, then either n = k + 1 and p = E(k/2), or n = k + 2 and p = P(k/2 + 1).",
        H("An exhausted lower chain"),
        Blocks(
            Node("pop-stack-popstackmaximumterminal-exhausted-lower-prefix", "An exhausted lower chain", "exhausted_lower_prefix",
                "Let p have size n at least four and maximum second. Assume the upper values after its first two entries decrease, no lower value has both a smaller and a larger lower value later, and adjacent values are never consecutive, where upper and lower are relative to its first entry. If the minimum has even zero-based position k at least two and the first entry equals k/2 + 1, then either n = k + 1 and p = E(k/2), or n = k + 2 and p = P(k/2 + 1).", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}

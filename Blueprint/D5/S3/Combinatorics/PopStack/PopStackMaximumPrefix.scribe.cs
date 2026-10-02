using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PopStack;

internal sealed class PopStackMaximumPrefixDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PopStack/PopStackMaximumPrefix.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/cioni2025sorting");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Let p be a permutation of size n at least four with maximum second, and write a for its first entry. In the suffix after its first two entries, assume values above a decrease and no value below a has both a smaller and a larger such value later. If adjacent entries never have consecutive values and the minimum has zero-based position k, then every entry before k is prescribed: at even position i it equals a minus i/2, and at odd position i it equals n minus floor(i/2).",
        H("The alternating prefix before the minimum"),
        Blocks(
            Node("pop-stack-popstackmaximumprefix-maximum-second-prefix", "The alternating prefix before the minimum", "maximum_second_prefix",
                "Let p be a permutation of size n at least four with maximum second, and write a for its first entry. In the suffix after its first two entries, assume values above a decrease and no value below a has both a smaller and a larger such value later. If adjacent entries never have consecutive values and the minimum has zero-based position k, then every entry before k is prescribed: at even position i it equals a minus i/2, and at odd position i it equals n minus floor(i/2).", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}

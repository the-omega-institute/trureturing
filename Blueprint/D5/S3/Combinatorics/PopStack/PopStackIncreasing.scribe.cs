using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PopStack;

internal sealed class PopStackIncreasingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PopStack/PopStackIncreasing.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/cioni2025sorting");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Let a word in C consist of a prefix, the entry one, and a suffix, with every entry of the prefix and suffix at least two. Increasing all those other entries by one and replacing the minimum by the adjacent entries one and two preserves membership in C.",
        H("Increasing inflation of the minimum"),
        Blocks(
            Node("pop-stack-popstackincreasing-increasing-minimum-inflation", "Increasing inflation of the minimum", "increasing_minimum_inflation",
                "Let a word in C consist of a prefix, the entry one, and a suffix, with every entry of the prefix and suffix at least two. Increasing all those other entries by one and replacing the minimum by the adjacent entries one and two preserves membership in C.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}

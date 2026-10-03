using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Nonnesting;

internal sealed class NonnestingFourLargeFirstDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Nonnesting/NonnestingFourLargeFirst.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/elizalde2024pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A large initial value repeats immediately and determines a value cut.",
        H("A Large Initial Letter"),
        Blocks(
            Node("nonnesting-nonnestingfourlargefirst-large-first-double", "Immediate repetition of a large first letter", "large_first_double",
                "An avoider beginning with k at least three has a second k immediately after the first.", DescribeRole.Theorem),
            Node("nonnesting-nonnestingfourlargefirst-large-first-cut", "Cut after a large initial block", "large_first_cut",
                "If an avoider begins with k at least three and below n, it has a value cut at k.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}

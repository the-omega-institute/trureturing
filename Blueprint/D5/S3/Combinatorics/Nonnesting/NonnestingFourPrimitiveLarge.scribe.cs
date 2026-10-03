using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Nonnesting;

internal sealed class NonnestingFourPrimitiveLargeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Nonnesting/NonnestingFourPrimitiveLarge.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/elizalde2024pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The largest-letter prefix is primitive and leaves an ordered avoider.",
        H("Removing the Doubled Largest Prefix"),
        Blocks(
            Node("nonnesting-nonnestingfourprimitivelarge-primitive-large-prefix", "Primitivity of the largest prefix", "primitive_large_prefix",
                "A word beginning with two copies of its largest letter has no proper value cut.", DescribeRole.Theorem),
            Node("nonnesting-nonnestingfourprimitivelarge-large-first-tail", "Tail after the largest prefix", "large_first_tail",
                "Removing the two initial largest letters from such an avoider leaves an avoider of size one less with increasing first-occurrence order.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}

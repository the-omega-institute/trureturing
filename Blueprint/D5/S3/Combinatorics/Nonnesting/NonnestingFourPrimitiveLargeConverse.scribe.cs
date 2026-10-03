using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Nonnesting;

internal sealed class NonnestingFourPrimitiveLargeConverseDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Nonnesting/NonnestingFourPrimitiveLargeConverse.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/elizalde2024pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An increasing-order tail yields an avoider after a doubled largest prefix.",
        H("Adding the Doubled Largest Prefix"),
        Blocks(
            Node("nonnesting-nonnestingfourprimitivelargeconverse-large-prefix-construct", "Constructing a large-prefix avoider", "large_prefix_construct",
                "For n at least two, prefixing an increasing-order avoider of size n minus one with two copies of n gives a four-pattern avoider of size n.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}

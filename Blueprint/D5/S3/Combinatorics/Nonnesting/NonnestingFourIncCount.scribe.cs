using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Nonnesting;

internal sealed class NonnestingFourIncCountDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Nonnesting/NonnestingFourIncCount.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/elizalde2024pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Increasing first-occurrence order admits a binary extension at each positive size.",
        H("Counting Increasing-Order Words"),
        Blocks(
            Node("nonnesting-nonnestingfourinccount-increasingwords", "Words with increasing first occurrences", "increasingWords",
                "These are four-pattern avoiders whose first occurrences follow increasing letter order.", DescribeRole.Definition),
            Node("nonnesting-nonnestingfourinccount-increasingstep", "Binary extension equivalence", "increasingStep",
                "For positive n, a choice of one of two extensions and a word of size n correspond bijectively to an increasing-order word of size n plus one.", DescribeRole.Definition),
            Node("nonnesting-nonnestingfourinccount-increasingwords-card", "Cardinality of increasing-order words", "increasingWords_card",
                "For positive n, the number of increasing-order words of size n is two to the power n minus one.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}

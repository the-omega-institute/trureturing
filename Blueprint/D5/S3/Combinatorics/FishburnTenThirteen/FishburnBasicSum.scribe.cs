using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.FishburnTenThirteen;

internal sealed class FishburnBasicSumDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/FishburnTenThirteen/FishburnBasicSum.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/egge2022pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Fishburn condition is preserved and reflected by direct sums with separated values.",
        H("The Fishburn Condition under Direct Sum"),
        Blocks(
            Node("fishburnbasicsum-isfishburn-directsum-iff", "Componentwise Fishburn condition", "isFishburn_directSum_iff",
                "Let m be a nonnegative integer, let every entry of a word u be at most m, and let every entry of a word v be positive. The concatenation of u with the word obtained by increasing every entry of v by m is Fishburn if and only if both u and v are Fishburn.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}

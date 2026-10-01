using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Nonnesting;

internal sealed class NonnestingOneThreeTwoTwoCountDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwoCount.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/elizalde2024pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Terminal factorization decomposes weighted counts on every nonempty finite alphabet.",
        H("Weighted Terminal Enumeration"),
        Blocks(
            Node("nonnesting-nonnestingonethreetwotwocount-weighted-decomposition", "Weighted decomposition by pivot and cut", "weighted_decomposition",
                "For a nonempty alphabet with distinct entries and any weight function from natural numbers to an additive commutative monoid, sum the weights of the lengths after the last first occurrence over doubled nonnesting words avoiding 1322. This sum equals the sum over pivots of two contributions. Type I ranges over upper and lower words and cuts at most the lower length following every lower first occurrence, with weight at lower length minus cut plus one. Type II ranges over upper words and cuts strictly below the upper length following every upper first occurrence, with weight at upper length minus cut plus lower alphabet size plus one, multiplied by the Catalan number of the lower alphabet size.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}

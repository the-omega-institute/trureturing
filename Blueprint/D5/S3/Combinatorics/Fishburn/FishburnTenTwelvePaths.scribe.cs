using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Fishburn;

internal sealed class FishburnTenTwelvePathsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Fishburn/FishburnTenTwelvePaths.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/egge2022pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Mathematical definitions and results for Fishburn permutations and classical pattern avoidance.",
        H("FishburnTenTwelvePaths"),
        Blocks(
            Node("fishburntentwelvepaths-positivehistory-def", "Definition PositiveHistory", "PositiveHistory", "This definition specifies a mathematical object used in the Fishburn permutation construction.", DescribeRole.Definition),
            Node("fishburntentwelvepaths-walk-def", "Definition Walk", "Walk", "This definition specifies a mathematical object used in the Fishburn permutation construction.", DescribeRole.Definition),
            Node("fishburntentwelvepaths-positive-history-walk-theorem", "Theorem positive_history_walk", "positive_history_walk", "This theorem establishes the stated mathematical relation for Fishburn permutations and classical pattern avoidance.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}

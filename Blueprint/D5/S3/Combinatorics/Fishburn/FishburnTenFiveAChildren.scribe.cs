using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Fishburn;

internal sealed class FishburnTenFiveAChildrenDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Fishburn/FishburnTenFiveAChildren.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/egge2022pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Mathematical definitions and results for Fishburn permutations and classical pattern avoidance.",
        H("FishburnTenFiveAChildren"),
        Blocks(
            Node("fishburntenfiveachildren-state-def", "Definition State", "State", "This definition specifies a mathematical object used in the Fishburn permutation construction.", DescribeRole.Definition),
            Node("fishburntenfiveachildren-edgelabel-def", "Definition edgeLabel", "edgeLabel", "This definition specifies a mathematical object used in the Fishburn permutation construction.", DescribeRole.Definition),
            Node("fishburntenfiveachildren-edgeindex-def", "Definition edgeIndex", "edgeIndex", "This definition specifies a mathematical object used in the Fishburn permutation construction.", DescribeRole.Definition)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}

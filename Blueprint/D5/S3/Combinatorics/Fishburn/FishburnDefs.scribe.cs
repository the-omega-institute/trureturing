using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Fishburn;

internal sealed class FishburnDefsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Fishburn/FishburnDefs.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/egge2022pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Mathematical definitions and results for Fishburn permutations and classical pattern avoidance.",
        H("FishburnDefs"),
        Blocks(
            Node("fishburndefs-isfishburn-def", "Definition IsFishburn", "IsFishburn", "This definition specifies a mathematical object used in the Fishburn permutation construction.", DescribeRole.Definition),
            Node("fishburndefs-avoiders-def", "Definition avoiders", "avoiders", "This definition specifies a mathematical object used in the Fishburn permutation construction.", DescribeRole.Definition),
            Node("fishburndefs-claim104-def", "Definition claim104", "claim104", "This definition specifies a mathematical object used in the Fishburn permutation construction.", DescribeRole.Definition),
            Node("fishburndefs-claim105-def", "Definition claim105", "claim105", "This definition specifies a mathematical object used in the Fishburn permutation construction.", DescribeRole.Definition)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}

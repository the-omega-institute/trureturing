using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Fishburn;

internal sealed class FishburnClassicalDefsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Fishburn/FishburnClassicalDefs.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/egge2022pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Mathematical definitions and results for Fishburn permutations and classical pattern avoidance.",
        H("FishburnClassicalDefs"),
        Blocks(
            Node("fishburnclassicaldefs-classicalavoiders-def", "Definition classicalAvoiders", "classicalAvoiders", "This definition specifies a mathematical object used in the Fishburn permutation construction.", DescribeRole.Definition),
            Node("fishburnclassicaldefs-claim109-def", "Definition claim109", "claim109", "This definition specifies a mathematical object used in the Fishburn permutation construction.", DescribeRole.Definition),
            Node("fishburnclassicaldefs-claim1011-def", "Definition claim1011", "claim1011", "This definition specifies a mathematical object used in the Fishburn permutation construction.", DescribeRole.Definition),
            Node("fishburnclassicaldefs-claim1012-def", "Definition claim1012", "claim1012", "This definition specifies a mathematical object used in the Fishburn permutation construction.", DescribeRole.Definition)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}

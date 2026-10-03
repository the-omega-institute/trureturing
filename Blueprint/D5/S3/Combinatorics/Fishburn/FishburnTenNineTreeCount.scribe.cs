using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Fishburn;

internal sealed class FishburnTenNineTreeCountDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Fishburn/FishburnTenNineTreeCount.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/egge2022pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Mathematical definitions and results for Fishburn permutations and classical pattern avoidance.",
        H("FishburnTenNineTreeCount"),
        Blocks(
            Node("fishburntenninetreecount-descendants-def", "Definition descendants", "descendants", "This definition specifies a mathematical object used in the Fishburn permutation construction.", DescribeRole.Definition),
            Node("fishburntenninetreecount-abstract-tree-enumeration-theorem", "Theorem abstract_tree_enumeration", "abstract_tree_enumeration", "This theorem establishes the stated mathematical relation for Fishburn permutations and classical pattern avoidance.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}

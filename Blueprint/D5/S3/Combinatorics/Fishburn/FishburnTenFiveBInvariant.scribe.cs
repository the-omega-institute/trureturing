using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Fishburn;

internal sealed class FishburnTenFiveBInvariantDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Fishburn/FishburnTenFiveBInvariant.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/egge2022pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Mathematical definitions and results for Fishburn permutations and classical pattern avoidance.",
        H("FishburnTenFiveBInvariant"),
        Blocks(
            Node("fishburntenfivebinvariant-all-b-site-invariant-theorem", "Theorem all_B_site_invariant", "all_B_site_invariant", "This theorem establishes the stated mathematical relation for Fishburn permutations and classical pattern avoidance.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}

using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.FishburnTenThirteen;

internal sealed class FishburnTenThirteenSitesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/FishburnTenThirteen/FishburnTenThirteenSites.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/egge2022pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Interval suffixes and separating cuts characterize active positions for Fishburn permutations avoiding 2413 and 2431.",
        H("Active Positions for 2413 and 2431 Avoiders"),
        Blocks(
            Node("fishburntenthirteensites-interval-active-sites", "The interval-suffix criterion", "interval_active_sites",
                "Let p be a Fishburn permutation of length n avoiding 2413 and 2431 and let s be a position from zero through its length. Inserting n + 1 at s preserves these conditions exactly when the values in the suffix beginning at s form an order-connected set of natural numbers and, whenever an entry immediately before s exists, it is not one greater than any entry at or after s. Order-connected means that every natural number between two suffix values is also a suffix value.", DescribeRole.Theorem),
            Node("fishburntenthirteensites-interval-site-updates", "Updating the interval positions", "interval_site_updates",
                "Let p be a Fishburn permutation of positive length n avoiding 2413 and 2431, and suppose insertion of n + 1 at position s preserves those conditions. For every gap g at most s, insertion of n + 2 at g in the resulting permutation is permitted exactly when every entry of p before g is less than every entry at or after g. Insertion immediately after n + 1 is permitted exactly when the original maximum n occurs before s in p. For every gap g strictly after s and at most the length of p, insertion of n + 2 at g + 1 in the resulting permutation is permitted exactly when insertion of n + 1 at g in p is permitted. Positions are numbered from zero.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}

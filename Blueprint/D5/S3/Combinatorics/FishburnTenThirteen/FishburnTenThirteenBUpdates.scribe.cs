using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.FishburnTenThirteen;

internal sealed class FishburnTenThirteenBUpdatesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/FishburnTenThirteen/FishburnTenThirteenBUpdates.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/egge2022pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two successive maximum insertions in the 2431 and 3241 avoidance class are controlled by inequalities across the insertion positions.",
        H("Updating Active Positions for 2431 and 3241 Avoiders"),
        Blocks(
            Node("fishburntenthirteenbupdates-crossing-site-updates", "Active positions after one insertion", "crossing_site_updates",
                "Let p be a Fishburn permutation of positive length n avoiding 2431 and 3241, and suppose insertion of n + 1 at position s preserves those conditions. For every gap g at most s, insertion of n + 2 at g in the resulting permutation is permitted exactly when g is active in p and every entry of p before g is less than every entry at or after s. For every gap g strictly after s and at most the length of p, insertion of n + 2 at g + 1 is permitted exactly when g is active in p and every entry from s through g - 1 is less than every entry at or after g. Insertion immediately after n + 1 is permitted exactly when the original maximum n occurs before s in p. If s is zero and p is assembled from a list of nonempty sum-indecomposable permutation components, the resulting permutation has as many active positions as there are components plus one. Positions are numbered from zero.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}

using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.FishburnTenThirteen;

internal sealed class FishburnTenThirteenBSumsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/FishburnTenThirteen/FishburnTenThirteenBSums.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/egge2022pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Maximum-insertion positions in a direct sum avoiding 2431 and 3241 are determined componentwise.",
        H("Active Positions in Direct Sums Avoiding 2431 and 3241"),
        Blocks(
            Node("fishburntenthirteenbsums-crossing-sum-sites", "Componentwise insertion and crossing inequalities", "crossing_sum_sites",
                "Let u and v be Fishburn permutations of lengths m and n avoiding 2431 and 3241, and suppose their direct sum avoids the same patterns and is Fishburn. For every position s from zero through m, insertion of m + n + 1 at s in the direct sum preserves these conditions exactly when insertion of m + 1 at s in u does so. For every position s from zero through n, insertion at m + s in the direct sum is permitted exactly when insertion of n + 1 at s in v is permitted. Moreover, if the entry at a position h in the direct sum is m + n and a permitted insertion position s is strictly after h, every entry strictly between h and s is less than every entry at or after s. Positions are numbered from zero.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}

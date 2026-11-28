using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Parking;

internal sealed class BackgammonIncreasingPrefixDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Combinatorics/Parking/BackgammonIncreasingPrefix.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/PermutationPatterns/cliftonharriskhaqan2026parking");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "First-car deletion and insertion describe backgammon parking words.",
        H("Backgammon parking and first-car insertion"),
        Blocks(
            Node("backgammonOutcome", "Backgammon outcome", DescribeRole.Definition,
                "Cars arrive in label order. The arriving car takes its preference and sends any incumbent to the least vacant spot. Read car labels in spot order.",
                AssessedProvenance.FromLiterature(Source)),
            Node("backgammon_first_car_insertion", "Insert car one in spot one", DescribeRole.Theorem,
                "For a valid reduced word, increase every old preference by one. The new initial preference is either one or one more than an entry of the reduced word's longest distinct initial prefix. These are exactly the valid words with this shifted tail and with car one occupying the first spot of the shifted outcome.",
                AssessedProvenance.FromRepo(Source)),
            Node("backgammon_lift_statistic", "Rank of an inserted word", DescribeRole.Theorem,
                "The lifts of a valid word occur without duplicates and give exactly one word of each longest distinct initial prefix length from one through one more than the reduced word's rank.",
                AssessedProvenance.FromRepo(Source))),
        []));

    private static DocumentBlock Node(
        string declaration, string title, DescribeRole role, string prose, AssessedProvenance provenance) =>
        Describe.Lean(
            DescribeId.Create("backgammon-parking-" + declaration.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create(Owner + declaration),
            H(title),
            StatementSource.WithoutFormula(),
            provenance,
            Blocks(Paragraph(Text(prose))),
            role);
}

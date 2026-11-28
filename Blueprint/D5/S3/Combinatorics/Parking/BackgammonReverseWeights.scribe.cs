using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Parking;

internal sealed class BackgammonReverseWeightsDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Combinatorics/Parking/BackgammonReverseWeights.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/PermutationPatterns/cliftonharriskhaqan2026parking");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "First-car deletion and the final arrival give exact recurrences for backgammon parking words.",
        H("Increasing prefixes and reverse outcomes"),
        Blocks(
            Node("increasingPrefix_count", "Count by deleting the increasing prefix", DescribeRole.Theorem,
                "Delete the fixed prefix of k cars. Each shorter reverse-outcome word of rank r contributes the number of k successive lifts from rank r. A lift has one word of each rank from 1 through r + 1.",
                AssessedProvenance.FromRepo(Source)),
            Node("reverseOutcome_weight_succ_succ", "Two cases for a reverse outcome", DescribeRole.Theorem,
                "If car 1 starts in the final spot, deleting it leaves a reverse word and lowers the rank by one. Otherwise the final arrival bumps car 1 from spot 1 into the final vacancy. The preceding word is a one-car lift of a reverse word two cars shorter, and appending preference 1 preserves its rank.",
                AssessedProvenance.FromRepo(Source)),
            Node("refinedCount_reverse_succ_succ", "Count by longest distinct prefix", DescribeRole.Theorem,
                "The number at length m + 2 and rank j + 1 is the number at length m + 1 and rank j plus the sum at length m over ranks j through m. An empty street has one word of rank zero.",
                AssessedProvenance.FromLiterature(Source)),
            Node("increasingPrefix_count_diagonal", "The empty suffix", DescribeRole.Theorem,
                "When the increasing prefix fills the street, its fiber is counted by the number of iterated lifts of the unique empty word.",
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

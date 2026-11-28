using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Parking;

internal sealed class BackgammonMotzkinPathsDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Combinatorics/Parking/BackgammonMotzkinPaths.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/PermutationPatterns/cliftonharriskhaqan2026parking");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The reverse backgammon recurrence agrees with the ground-return recurrence for ordinary Motzkin walks.",
        H("Reverse parking outcomes and Motzkin walks"),
        Blocks(
            Node("trace", "Scan a Motzkin step word", DescribeRole.Definition,
                "The scan counts each arrival at height zero, including the final endpoint of a nonempty walk. A down step at height zero fails.",
                AssessedProvenance.FromRepo(Source)),
            Node("mem_motzkinWalks", "Literal Motzkin walks", DescribeRole.Theorem,
                "At length m the enumerator contains precisely the words that never leave nonnegative height and finish at height zero.",
                AssessedProvenance.FromLiterature(Source)),
            Node("motzkinWalks_nodup", "Each step word occurs once", DescribeRole.Theorem,
                "An upward first step determines the unique return that closes the first arch, and the cut fixes its interior and the remaining walk.",
                AssessedProvenance.FromRepo(Source)),
            Node("walkWeight_succ_succ", "Ground returns under horizontal steps and arches", DescribeRole.Theorem,
                "An initial horizontal step adds one ground return. To create an initial arch, cut a shorter walk at any ground visit, using both endpoints as possible cuts. The cut leaves one resulting walk of each rank from 1 through one more than the shorter walk's rank.",
                AssessedProvenance.FromRepo(Source)),
            Node("reverseOutcome_weight_eq_motzkin", "Equality by rank", DescribeRole.Theorem,
                "Every weight on the longest distinct initial preference length gives the same sum as the weight on ground returns. For nonempty walks, the rank exceeds the number of interior touches by one.",
                AssessedProvenance.FromRepo(Source)),
            Node("reverseOutcome_count_eq_motzkin", "The reverse outcome", DescribeRole.Theorem,
                "Unit weights give the Motzkin number for every reverse-outcome length, including the empty case.",
                AssessedProvenance.FromLiterature(Source)),
            Node("increasingPrefix_count_eq_motzkin", "Weighted Motzkin formula for an increasing prefix", DescribeRole.Theorem,
                "For n ≥ k ≥ 0, sum the k-lift counts over the Motzkin walks of length n − k, using the number of returns as the starting rank. At n = k the empty walk contributes the k-lift count at rank zero.",
                AssessedProvenance.FromRepo(Source))),
        []));

    private static DocumentBlock Node(
        string declaration, string title, DescribeRole role, string prose, AssessedProvenance provenance) =>
        Describe.Lean(
            DescribeId.Create("backgammon-motzkin-" + declaration.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create(Owner + declaration),
            H(title),
            StatementSource.WithoutFormula(),
            provenance,
            Blocks(Paragraph(Text(prose))),
            role);
}

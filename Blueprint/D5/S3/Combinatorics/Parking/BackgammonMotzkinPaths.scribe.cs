using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Parking;

internal sealed class BackgammonMotzkinPathsDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Combinatorics/Parking/BackgammonMotzkinPaths.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/PermutationPatterns/cliftonharriskhaqan2026parking");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The ground-return recurrence for ordinary Motzkin walks gives weighted and signed counts of increasing-prefix backgammon outcomes.",
        H("Backgammon outcomes and Motzkin walks"),
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
                "An initial horizontal step adds one ground return. To create an initial arch, cut a shorter walk at any ground visit, using both endpoints as possible cuts. The cut leaves one resulting walk of each rank from 1 through one more than the shorter walk's rank. This is the weighted form of Lemma 3.18, equation (5), of Clifton, Harris and Khaqan.",
                AssessedProvenance.FromRepo(Source)),
            Node("reverseOutcome_weight_eq_motzkin", "Equality by rank", DescribeRole.Theorem,
                "Every weight on the longest distinct initial preference length gives the same sum as the weight on ground returns. This uses the refinement in the proof of Theorem 1.8. For nonempty walks, the rank exceeds the number of interior touches by one.",
                AssessedProvenance.FromRepo(Source)),
            Node("reverseOutcome_count_eq_motzkin", "The reverse outcome", DescribeRole.Theorem,
                "Unit weights give the Motzkin number for every reverse-outcome length, including the empty case.",
                AssessedProvenance.FromLiterature(Source)),
            Node("increasingPrefix_count_eq_motzkin", "Weighted Motzkin formula for an increasing prefix", DescribeRole.Theorem,
                "For n ≥ k ≥ 0, sum the k-lift counts over the Motzkin walks of length n − k, using the number of returns as the starting rank. At n = k the empty walk contributes the k-lift count at rank zero.",
                AssessedProvenance.FromRepo(Source)),
            Node("liftCatalan_spec", "Catalan numbers from the lift counts", DescribeRole.Theorem,
                "The k-lift count at rank zero is the kth Catalan number Cₖ. Shifting the starting rank by one sends the k-lift weight to the sum of the (k − i)-lift weights with coefficients Cᵢ for 0 ≤ i ≤ k. At rank zero this identity gives the Catalan convolution, with C₀ = 1.",
                AssessedProvenance.FromRepo(Source)),
            Node("signedCoefficients", "Integer shift coefficients", DescribeRole.Definition,
                "In increasing order of offset from n − k, the coefficient list represents Qₖ(T), with Q₀ = 1 and Qₖ₊₁ = T² Qₖ − T times the sum of Cᵢ Qₖ₋ᵢ for 0 ≤ i ≤ k. The Laurent shift polynomial for offsets from n is T⁻ᵏ Qₖ(T).",
                AssessedProvenance.FromRepo(Source)),
            Node("signedCoefficients_shape", "Range of shifts", DescribeRole.Theorem,
                "The list has length 2k + 1 and its last coefficient is one. For k ≥ 1 the first coefficient is zero, so the nonzero shifts from n lie in [1 − k, k].",
                AssessedProvenance.FromRepo(Source)),
            Node("increasingPrefix_count_eq_signed_motzkin", "Signed Motzkin formula for Question 5.2", DescribeRole.Theorem,
                "For all n ≥ k ≥ 0, the coefficient at offset j weights the Motzkin number M(n − k + j). The ground-return recurrence and the Catalan rank shift give the recurrence for Qₖ, including an empty suffix. For k = 0, 1 and 2 this yields M(n), M(n + 1) − M(n), and M(n + 2) − 2M(n + 1) + M(n) − M(n − 1), as in Theorem 1.8 and Corollaries 1.9–1.10 of Clifton, Harris and Khaqan on their respective ranges. At n = k the signed sum equals Cₖ, with value one at n = k = 0.",
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

using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

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
                "Read the list from the constant term upward as the coefficients of Qₖ(T). Here Cᵢ is the Catalan number liftCatalan(i). The recurrence first shifts the previous coefficient list by two positions, then subtracts the Catalan-weighted lists shifted by one position. The Laurent polynomial for offsets from n has the coefficients of Qₖ shifted down by k.",
                AssessedProvenance.FromRepo(Source), CoefficientRecurrence()),
            Node("signedCoefficients_shape", "Range of shifts", DescribeRole.Theorem,
                "The list has length 2k + 1 and its last coefficient is one. For k ≥ 1 the first coefficient is zero, so the nonzero shifts from n lie in [1 − k, k].",
                AssessedProvenance.FromRepo(Source)),
            Node("increasingPrefix_count_eq_signed_motzkin", "Signed Motzkin formula for Question 5.2", DescribeRole.Theorem,
                "Clifton, Harris and Khaqan ask in Question 5.2 for a sum involving Motzkin numbers with indices depending on n, for each fixed k and n > k. The target outcome has the labels 1 through k in increasing order followed by the remaining labels in decreasing order. The formula holds for all n ≥ k ≥ 0. Vertical bars count list entries, the square brackets index signedCoefficients from zero, and the arithmetic of the sum is over the integers. "
                    + "The ground-return recurrence and the Catalan rank shift give the recurrence for Qₖ. For k = 0, 1 and 2 the formula yields M(n), M(n + 1) − M(n), and M(n + 2) − 2M(n + 1) + M(n) − M(n − 1), where M counts ordinary Motzkin walks. These are Theorem 1.8 and Corollaries 1.9–1.10 on their published ranges. At n = k the suffix is empty and the sum is Cₖ, agreeing with the identity-permutation case of Theorem 1.6 for positive k. The empty street contributes one.",
                AssessedProvenance.FromRepo(Source), SignedFormula())),
        []));

    private static DocumentBlock Node(
        string declaration, string title, DescribeRole role, string prose, AssessedProvenance provenance,
        Formula? formula = null) =>
        Describe.Lean(
            DescribeId.Create("backgammon-motzkin-" + declaration.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create(Owner + declaration),
            H(title),
            formula is null ? StatementSource.WithoutFormula() : StatementSource.FromAuthor(formula),
            provenance,
            Blocks(Paragraph(Text(prose))),
            role);

    private static Formula CoefficientRecurrence()
    {
        var k = F.Id("k");
        var i = F.Id("i");
        var t = F.Id("T");
        Formula At(string name, Formula index) => Seq(F.Id(name), Underscore, Grp(index));
        return Disp(Seq(
            At("Q", D(0)), Eq, D(1), Comma, Quad, Sp,
            At("Q", Add(k, D(1))), Eq, new Formula.Power(t, D(2)), At("Q", k), Minus, t,
            Sum, Underscore, Grp(i, Eq, D(0)), Caret, Grp(k), Sp,
            At("C", i), At("Q", Subtract(k, i))));
    }

    private static Formula SignedFormula()
    {
        var n = F.Id("n");
        var k = F.Id("k");
        var j = F.Id("j");
        var suffixLength = Subtract(n, k);
        var outcome = Call("withIncreasingPrefix", k, Call("reverseOutcome", suffixLength));
        return Disp(Seq(
            Bar, Call("outcomeWords", outcome), Bar, Eq,
            Sum, Underscore, Grp(j, Eq, D(0)), Caret, Grp(D(2), k), Sp,
            Call("signedCoefficients", k), OpenBracket, j, CloseBracket, Cdot,
            Bar, Call("motzkinWalks", Add(suffixLength, j)), Bar,
            Comma, Quad, Sp, n, Geq, Sp, k, Geq, D(0)));
    }
}

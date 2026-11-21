using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class RoundedNormBoundedErrorDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/RoundedNormBoundedError.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceAlgebraic/mazhang2026a400645siblings");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Rounded two- and three-norm sequences satisfy x_n = C R^(n/2) + O(1) with C > 0, "
            + "exactly for the seeds that do not stall.",
        H("Rounded two- and three-norm sequences"),
        Blocks(
            Describe.Lean(DescribeId.Create("rounded-norm-bounded-error"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Bounded error for rounded norms"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "Let m = 2 or m = 3 and let x be a sequence of natural numbers with "
                        + "x_(n+m) = round √(x_n^2 + ⋯ + x_(n+m−1)^2) for every n, where round is "
                        + "nearest rounding. Let R be the root above one of "
                        + "y^m − y^(m−1) − ⋯ − 1: the golden ratio φ for m = 2 and the "
                        + "Tribonacci constant for m = 3. Then there is C > 0 with "
                        + "x_n − C R^(n/2) = O(1) and x_(n+1)/x_n − √R = O(R^(−n/2)) if and only "
                        + "if max(x_0, x_1) ≥ 2 for m = 2, and if and only if x_0 + x_1 + x_2 > 0 "
                        + "for m = 3.")),
                    Paragraph(Text(
                        "Proof. Write s_n = x_n^2 + ⋯ + x_(n+m−1)^2 and b_n = x_n^2. Nearest "
                        + "rounding gives |x_(n+m) − √s_n| ≤ 1/2, hence "
                        + "|b_(n+m) − s_n| ≤ √s_n + 1/4, and x_(n+m) ≥ x_(n+i) for each i < m, so "
                        + "x is nondecreasing from index m − 1. If the window starts at k with "
                        + "k + 1/4 < (m − 1)k^2, then s_n ≥ m k^2 > (k + 1/2)^2 and "
                        + "x_(n+m) ≥ k + 1; this holds for k ≥ 2 when m = 2 and for k ≥ 1 when "
                        + "m = 3. Under the seed conditions some entry from index m − 1 on "
                        + "reaches that threshold, so x grows by one every m steps and s_n → ∞.")),
                    Paragraph(Text(
                        "Once √s_n + 1/4 is a small fraction of s_n, b satisfies "
                        + "b_(n+m) ≤ K s_n and b_(n+m) ≥ K′ s_n with K = 4/3, K′ = 9/10 for m = 2 and "
                        + "K = 8/7, K′ = 3/4 for m = 3. Comparing with the geometric sequences "
                        + "2^n (K(1 + ⋯ + 2^(m−1)) ≤ 2^m) and (3/2)^n "
                        + "((3/2)^m ≤ K′(1 + ⋯ + (3/2)^(m−1))) gives b_n = O(2^n) and b_n ≥ M (3/2)^n "
                        + "with M > 0. The characteristic polynomial has the simple root R and "
                        + "its other roots have modulus below one: 1 − φ for m = 2, and for "
                        + "m = 3 the roots of y^2 + (R − 1)y + R^2 − R − 1, a complex pair of "
                        + "squared modulus R^2 − R − 1 < 1 since R < 2. Dominant-root forcing "
                        + "(D5/S1/Recurrence/Asymptotic/DominantRootForcing) with forcing "
                        + "O(2^(n/2)) gives b_n = L R^n + O(2^(n/2)), so b_n − L R^n = o(R^n) and "
                        + "b_n = O(R^n); the forcing is then O(R^(n/2)) and the same theorem gives "
                        + "b_n = L R^n + O(R^(n/2)). Since 2^(1/2) < 3/2, L ≤ 0 would contradict "
                        + "b_n ≥ M (3/2)^n, so L > 0. Rationalizing, x_n − √L R^(n/2) = "
                        + "(b_n − L R^n)/(x_n + √L R^(n/2)) = O(1), and "
                        + "x_(n+1) − √R x_n is bounded while x_n ≥ (√L/2) R^(n/2), which gives the "
                        + "ratio rate.")),
                    Paragraph(Text(
                        "Conversely, if max(x_0, x_1) ≤ 1 for m = 2 then every x_n ≤ 1, since "
                        + "round √2 = 1; and a zero seed for m = 3 keeps x identically zero. In "
                        + "both cases x is bounded, which no C R^(n/2) + O(1) with C > 0 is. This "
                        + "is Corollary 5 in Section 4 of H. Ma and W. Zhang's note on OEIS "
                        + "A400645 (DOI 10.5281/zenodo.24369110), which assumes nondecreasing "
                        + "data with x_1 ≥ 2 for m = 2 and x_2 ≥ 1 for m = 3. It covers Henry "
                        + "Bottomley's A063827 (seed 1, 2) and Bernáth's A400644 (seed 0, 0, 1). "
                        + "Rounding ties never occur, since √s is not a half-integer for an "
                        + "integer s. Larger m would need every other root of "
                        + "y^m − y^(m−1) − ⋯ − 1 inside the unit disk, which is not formalized "
                        + "here."))),
                DescribeRole.Theorem))));
}

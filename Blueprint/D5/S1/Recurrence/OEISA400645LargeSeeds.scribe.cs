using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class OEISA400645LargeSeedsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/OEISA400645LargeSeeds.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceAlgebraic/mazhang2026a400645siblings");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every seed with a_1 ≤ a_2 ≤ a_3 the signed A400645 rule has nonnegative "
            + "radicands, and a_n = c λ^n + O(1) with c > 0 unless the seed is (0,0,0,0) or "
            + "(1,1,1,1).",
        H("The signed A400645 rule for every seed with a_1 ≤ a_2 ≤ a_3"),
        Blocks(
            Describe.Lean(DescribeId.Create("a400645-large-seeds"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Classification of seeds"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "Let a_1 ≤ a_2 ≤ a_3 and a_4 be nonnegative integers and, for n ≥ 4, "
                        + "a_(n+1) = round √s_n with s_n = a_n^2 + a_(n−1)^2 + a_(n−2)^2 − "
                        + "a_(n−3)^2. Let r be the largest real root of y^4 − y^3 − y^2 − y + 1 "
                        + "and λ = √r. Then (i) s_n ≥ 0 for every n ≥ 4, so the rule is well "
                        + "defined; (ii) the seeds (0,0,0,0) and (1,1,1,1) give constant "
                        + "sequences; (iii) for every other seed there is c > 0 with "
                        + "a_n − c λ^n = O(1) and a_(n+1)/a_n − λ = O(λ^(−n)). The two constant "
                        + "seeds are exactly the seeds for which (iii) fails.")),
                    Paragraph(Text(
                        "Proof. The first radicand is s_4 ≥ a_4^2 + a_3^2 because a_1 ≤ a_2, "
                        + "so a_5 ≥ √s_4 − 1/2 gives a_5 ≥ max(a_3, a_4). By strong induction "
                        + "s_n ≥ a_n^2 for every n ≥ 4: the subtracted term a_(n−3)^2 is at "
                        + "most a_(n−2)^2 (n = 4, 5 by the seed, n ≥ 7 by induction) or at most "
                        + "a_(n−1)^2 (n = 6, since a_3 ≤ a_5). Hence a_(n+1) ≥ a_n for n ≥ 4, "
                        + "which also gives (i). For (ii), a constant window c, c, c, c has "
                        + "s_n = 2c^2, and round √0 = 0, round √2 = 1. If a_n ≥ 3 for some "
                        + "n ≥ 6, then s_n ≤ 3 a_n^2 ≤ (7a_n/4)^2, so a_(n+1) ≤ 7a_n/4 + 1/2; "
                        + "since s_(n+1) ≥ a_(n+1)^2 + a_n^2 and a_n^2 > a_(n+1) + 1/4, one "
                        + "gets √s_(n+1) > a_(n+1) + 1/2 and a_(n+2) > a_(n+1). Hence once a "
                        + "term reaches 3 the sequence tends to infinity.")),
                    Paragraph(Text(
                        "Every seed other than the two constant ones reaches 3. If all terms "
                        + "from index four stayed at most 2, a term equal to 2 would be "
                        + "followed by a window 2, 2, 2, 2 with s = 8 and next term "
                        + "round √8 = 3. If they stayed at most 1, then a_5 = 1 (otherwise "
                        + "a_3 = a_4 = 0 and the seed is (0,0,0,0)), and a_k = 0 followed by "
                        + "three ones occurs at k = 4, 3, 2 or 1 according as a_4, a_3, a_2 is "
                        + "the first zero from the right; this gives s = 3 and next term "
                        + "round √3 = 2.")),
                    Paragraph(Text(
                        "For (iii) put b_n = a_n^2. Then b_j − b_(j+1) − b_(j+2) − b_(j+3) + "
                        + "b_(j+4) = a_(j+4)^2 − s_(j+3) = e_j with |e_j| ≤ √s_(j+3) + 1/4 ≤ "
                        + "√(b_j + b_(j+1) + b_(j+2) + b_(j+3)) + 1/4. Once a_n ≥ 10, "
                        + "b_(n+3) ≤ (8/7)(b_n + b_(n+1) + b_(n+2)) and (9/10)(b_n + b_(n+1)) ≤ "
                        + "b_(n+2). The constants satisfy (8/7)(1 + 2 + 4) = 2^3, (3/2)^2 = "
                        + "(9/10)(1 + 3/2) and 2 < min(r^2, (3/2)^2). The root r is simple and "
                        + "the other roots have modulus below √r < √2 "
                        + "(D5/S1/Recurrence/OEISA400645BoundedError). The analytic core of "
                        + "D5/S1/Recurrence/RoundedNormBoundedError then gives b_n = L r^n + "
                        + "O(r^(n/2)) with L > 0, and rationalizing gives (iii) with c = √L. "
                        + "If the seed is constant, a bounded sequence cannot be within O(1) "
                        + "of c λ^n with c > 0 and λ > 1.")),
                    Paragraph(Text(
                        "The two order hypotheses are needed. For the seed (1, 0, 0, 0) the "
                        + "first radicand is −1. For the seed (1, 1, 0, 0) the first radicand "
                        + "is 0, so a_5 = 0, and the next radicand is −1. No order is "
                        + "assumed between a_3 and a_4.")),
                    Paragraph(Text(
                        "This is Corollary 4 in Section 4 of H. Ma and W. Zhang's note on "
                        + "OEIS A400645 (DOI 10.5281/zenodo.24369110), which assumes a_4 ≥ 292 "
                        + "for a nondecreasing seed and gives the bounded error. Here the "
                        + "threshold is replaced by the exact condition on the seed, the "
                        + "assumption a_3 ≤ a_4 is dropped, and the ratio rate is added."))),
                DescribeRole.Theorem))));
}

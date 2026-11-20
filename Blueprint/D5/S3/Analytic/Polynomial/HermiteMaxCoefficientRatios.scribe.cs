using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Polynomial;

internal sealed class HermiteMaxCoefficientRatiosDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/Polynomial/HermiteMaxCoefficientRatios.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceAlgebraic/mazhang2026hermitesignedmode");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The signed and absolute maximal Hermite coefficients have closed forms, explicit successive "
            + "ratios, B(n)/M(n) → 1, and B(n + 1)/(B(n)√n) and M(n + 1)/(M(n)√n) both tend to √2.",
        H("Ratio limits of the maximal Hermite coefficients"),
        Blocks(
            Describe.Lean(DescribeId.Create("hermite-max-ratios-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Closed forms, exact ratios and limits of B(n) and M(n)"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "Let B(n) be the largest signed coefficient of the physicists' H_n, attained at "
                        + "a(n) = n − 4q(n), and M(n) the largest absolute coefficient, attained at "
                        + "b(n) = n − 2t(n). Then B(n) = n! 2^{a(n)}/((2q(n))! a(n)!) and "
                        + "M(n) = n! 2^{b(n)}/(t(n)! b(n)!), so 0 < B(n) ≤ M(n) and the denominators "
                        + "B(n)√n and M(n)√n are positive for n ≥ 1. The ratio B(n)/M(n) is 1 when a(n) = b(n), "
                        + "4t/((b + 1)(b + 2)) when a(n) = b(n) + 2, and b(b − 1)/(4(t + 1)) when "
                        + "a(n) = b(n) − 2. The successive ratio B(n + 1)/B(n) is 2(n + 1)/(a + 1) when "
                        + "q(n + 1) = q(n), and (n + 1)a(a − 1)(a − 2)/(8(2q + 1)(2q + 2)) with a ≥ 3 when "
                        + "q(n + 1) = q(n) + 1; M(n + 1)/M(n) is 2(n + 1)/(b + 1) when t(n + 1) = t(n), and "
                        + "(n + 1)b/(2(t + 1)) with b ≥ 1 when t(n + 1) = t(n) + 1. Consequently "
                        + "B(n)/M(n) → 1 and B(n + 1)/(B(n)√n) → √2, M(n + 1)/(M(n)√n) → √2.")),
                    Paragraph(Text(
                        "The closed forms are the coefficient formula of DLMF 18.5.13 at the two modes; the "
                        + "exact ratios follow by cancelling factorials, using that q and t step by 0 or 1 "
                        + "and the interlacing a(n) − b(n) ∈ {−2, 0, 2}. The explicit bounds "
                        + "−7/2 < a(n) − √(2n) < 3 and −5/2 < b(n) − √(2n) ≤ 0 give a(n)/√n → √2 and "
                        + "b(n)/√n → √2, hence q(n)/n → 1/4 and t(n)/n → 1/2. Each case expression, divided "
                        + "by √n where needed, is a continuous function of these normalized sequences with "
                        + "limit √2 or 1, and a sequence that at every degree equals one of finitely many "
                        + "case expressions with a common limit has that limit. This is Corollary 5, with "
                        + "equations (6) and (14), of H. Ma and W. Zhang (DOI 10.5281/zenodo.23957586) for "
                        + "OEIS A277280 and A277281 of V. Reshetnikov."))),
                DescribeRole.Theorem))));
}

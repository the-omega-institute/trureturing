using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Polynomial;

internal sealed class HermiteSignedModeThresholdDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/Polynomial/HermiteSignedModeThreshold.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceAlgebraic/mazhang2026hermitesignedmode");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The largest signed coefficient of the physicists' Hermite polynomial H_n is unique, at the "
            + "least j ≡ n (mod 4) with j² + 7j + 7 ≥ 2n.",
        H("The unique signed Hermite mode"),
        Blocks(
            Describe.Lean(DescribeId.Create("hermite-signed-mode-threshold-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Uniqueness, quadratic threshold and floor formula"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "Let a(n) be the least exponent maximizing the signed coefficients of H_n. Every "
                        + "other exponent k, including k > n, has a strictly smaller coefficient. Moreover "
                        + "a(n) is the least j ≡ n (mod 4) with j² + 7j + 7 ≥ 2n, and "
                        + "a(n) = n − 4⌊(2n + 7 − √(8n + 21))/8⌋.")),
                    Paragraph(Text(
                        "The positive coefficients are C_{n,r} = n! 2^{n−4r}/((2r)!(n − 4r)!) for 4r ≤ n; all "
                        + "others are nonpositive. With j = n − 4r, C_{n,r}/C_{n,r−1} = (j + 1)(j + 2)(j + 3)(j + 4)"
                        + "/(16(2r)(2r − 1)), and the ratio is never 1: numerator minus denominator is "
                        + "X² − Y² + 3 with X = j² + 5j + 5 ≥ 5 and Y = 8r − 2, which is positive for X ≥ Y and "
                        + "at most 2 − 2X < 0 otherwise. Hence C_{n,r} > C_{n,r−1} exactly when 8r ≤ j² + 5j + 7, "
                        + "that is j² + 7j + 7 ≥ 2n, so the coefficients rise strictly to a unique peak. Solving "
                        + "(2j + 7)² ≥ 8n + 21 gives the floor formula. The differences a(n + 1) − a(n) ∈ {1, −3} "
                        + "are the frozen HermiteSignedMode result. This is Theorem 1 of H. Ma and W. Zhang "
                        + "(DOI 10.5281/zenodo.23957586) on questions of Mike Sheppard in OEIS A381423."))),
                DescribeRole.Theorem))));
}

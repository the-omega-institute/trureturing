using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Polynomial;

internal sealed class HermiteAbsoluteModeThresholdDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/Polynomial/HermiteAbsoluteModeThreshold.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceAlgebraic/mazhang2026hermitesignedmode");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The absolute Hermite mode b(n) is the least j ≡ n (mod 2) with j² + 5j + 2 ≥ 2n, and the "
            + "absolute maximum is unique except at the tie degrees.",
        H("Threshold and uniqueness of the absolute Hermite mode"),
        Blocks(
            Describe.Lean(DescribeId.Create("hermite-absolute-threshold-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Quadratic threshold, at most two maxima, uniqueness off the tie degrees"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "Let b(n) be the least exponent of a largest absolute coefficient of the physicists' "
                        + "H_n. Then b(n) ≡ n (mod 2), and for every j ≡ n (mod 2), b(n) ≤ j exactly when "
                        + "j² + 5j + 2 ≥ 2n; so b(n) is the least such j. Every degree has either a unique "
                        + "absolute maximum or exactly two, and the maximum is unique exactly when the degree "
                        + "is not N_m = 2m(m + 2) + (m + 1)(−1)^{m+1} for some m ≥ 1.")),
                    Paragraph(Text(
                        "The nonzero absolute coefficients U_{n,k} = n! 2^{n−2k}/(k!(n − 2k)!) have consecutive "
                        + "ratios (j + 1)(j + 2)/(4k) with j = n − 2k, which are at least one exactly when "
                        + "j² + 5j + 2 ≥ 2n; this gives the threshold. The ratios strictly decrease, so the "
                        + "maximizers are among the last two qualifying indices, and two maxima occur exactly "
                        + "when a ratio equals one. The frozen HermiteAbsoluteTieOrders result identifies those "
                        + "degrees as N_m, and the frozen HermiteAbsoluteMode result gives b(n + 1) − b(n) = ±1. "
                        + "This is Theorem 3 of H. Ma and W. Zhang (DOI 10.5281/zenodo.23957586), on Mike "
                        + "Sheppard's conjectures in OEIS A381524 and A381737."))),
                DescribeRole.Theorem))));
}

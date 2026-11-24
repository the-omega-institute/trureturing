using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaExplicit;

internal sealed class GlobalZeroExpansionDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/ZetaExplicit/GlobalZeroExpansion.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A scaled disk estimate gives the centered zero expansion, and dyadic counts "
        + "supply the reciprocal-square summability it requires.",
        H("Centered logarithmic derivatives and global zero sums"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("scaled-disk-centered-log-derivative"),
                DeclarationHandle.Create(Owner + "logDeriv_partial_fraction_disk_centered"),
                H("Exact zeros and a quadratic radius denominator"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let f be entire with f(0) ≠ 0. Fix R > 0 and B ≥ 2, and assume "
                        + "‖f(w)‖ ≤ B · ‖f(0)‖ for ‖w‖ ≤ 24R/25. There is a single finite set "
                        + "Z of exactly the zeros of f in the closed disk of radius 22R/25. "
                        + "Write S(u) = ∑_{ρ ∈ Z} m(ρ)/(u − ρ), with m(ρ) the analytic order "
                        + "at ρ. For every ‖s‖ ≤ R/4 with f(s) ≠ 0, the norm of "
                        + "(logDeriv f s − logDeriv f 0) − (S(s) − S(0)) "
                        + "is at most 179180000 · ‖s‖ · log B / R².")),
                    Paragraph(Text(
                        "Apply logDeriv_partial_fraction_unit_centered to g(w) = f(Rw)/f(0). "
                        + "Multiplication by R carries its exact zero set to Z and preserves "
                        + "analytic orders. The chain rule and the scaled denominators give "
                        + "one factor of 1/R, and the evaluation norm ‖s/R‖ gives the other."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("global-centered-zero-expansion"),
                DeclarationHandle.Create(Owner + "logDeriv_global_zero_expansion"),
                H("An absolutely summable expansion over all actual zeros"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let f be entire with f(0) ≠ 0. Suppose that for all sufficiently "
                        + "large R one has B(R) ≥ 2 and ‖f(w)‖ ≤ B(R) · ‖f(0)‖ for "
                        + "‖w‖ ≤ 24R/25. Assume log B(R) = o(R²) and that m(ρ)/‖ρ‖² "
                        + "is summable over the actual zeros, with m(ρ) the analytic order. "
                        + "For every s with f(s) ≠ 0, the kernels "
                        + "m(ρ) · ((s − ρ)⁻¹ + ρ⁻¹) have summable norms and sum to "
                        + "logDeriv f s − logDeriv f 0.")),
                    Paragraph(Text(
                        "Outside the finite disk ‖ρ‖ ≤ 2‖s‖, combine the two reciprocals "
                        + "as s/((s − ρ)ρ). This bounds the kernel norm by "
                        + "2‖s‖ · m(ρ)/‖ρ‖². The exact disk cutoffs eventually contain "
                        + "every finite subset of the zeros, so their sums tend to the "
                        + "sum of the centered kernels. The scaled disk remainder tends to zero by "
                        + "log B(R) = o(R²)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("dyadic-multiplicity-reciprocal-square"),
                DeclarationHandle.Create(Owner + "summable_zero_multiplicity_div_norm_sq"),
                H("Reciprocal-square summability from dyadic zero counts"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let f be entire with f(0) ≠ 0 and the eventual normalized disk "
                        + "envelope B(R) above. If the series over natural n with terms "
                        + "log B(2^(n+2)/(22/25)) / (2^(n+1))² is summable, then "
                        + "m(ρ)/‖ρ‖² is summable over the actual zeros of f.")),
                    Paragraph(Text(
                        "The disk ‖ρ‖ ≤ 2 contributes a finite sum. Each remaining shell "
                        + "has 2^(n+1) < ‖ρ‖ ≤ 2^(n+2) and contains finitely many zeros. "
                        + "For sufficiently large n, the envelope applies at R = 2^(n+2)/(22/25). "
                        + "Landau's logDeriv_partial_fraction_disk then bounds the shell's "
                        + "multiplicities by log B(R) / log((24/25)/(22/25)). Dividing by "
                        + "the squared lower radius gives the summable tail majorant. The "
                        + "finitely many earlier shells contribute finite sums. The unique shell partition follows "
                        + "heightShell_partition in RightStripInverseHeight.lean."))),
                DescribeRole.Theorem))));
}

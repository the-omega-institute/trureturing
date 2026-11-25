using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaExplicit;

internal sealed class CenteredDiskLogDerivDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Centering the logarithmic derivative gives a remainder linear in the distance from zero.",
        H("Centered logarithmic derivative on the unit disk"),
        Blocks(Describe.Lean(
            DescribeId.Create("unit-disk-centered-log-derivative"),
            DeclarationHandle.Create(
                "D5/S3/Weil/ZetaExplicit/CenteredDiskLogDeriv.logDeriv_partial_fraction_unit_centered"),
            H("The finite zero sum and a linear remainder bound"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let f be analytic on a neighborhood of the closed unit disk, with f(0) = 1. "
                    + "Suppose B ≥ 2 and ‖f(w)‖ ≤ B on the closed disk of radius 24/25. "
                    + "There is a single finite set Z of exactly the zeros of f in the closed "
                    + "disk of radius 22/25. Put S(u) = ∑_{ρ ∈ Z} m(ρ)/(u − ρ), where m(ρ) is "
                    + "the analytic order of f at ρ. For every ‖z‖ ≤ 1/4 with f(z) ≠ 0, "
                    + "the norm of (logDeriv f z − logDeriv f 0) − (S(z) − S(0)) "
                    + "is at most 179180000 · ‖z‖ · log B.")),
                Paragraph(Text(
                    "Landau's norm_logDeriv_Cf_le bounds the logarithmic derivative of the "
                    + "zero-removed factor by 44795000 · log B. Subtract its value at zero "
                    + "to get a map from the disk of radius 1/2 into a closed disk of twice "
                    + "that bound. Mathlib's Complex.dist_le_div_mul_dist_of_mapsTo_ball "
                    + "supplies the factor ‖z‖/(1/2). Landau's logDeriv_split at z and at zero "
                    + "identifies the resulting difference with the centered remainder."))),
            DescribeRole.Theorem))));
}

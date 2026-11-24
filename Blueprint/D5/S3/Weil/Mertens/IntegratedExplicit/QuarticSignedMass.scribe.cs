using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit;

internal sealed class QuarticSignedMassDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/Mertens/IntegratedExplicit/QuarticSignedMass.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fourth-power samples recover either signed Mangoldt mass up to a logarithmic error.",
        H("Signed Mangoldt masses at fourth-power samples"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("quartic-grid-log-error"),
                DeclarationHandle.Create(Owner + "quartic_grid_log_error"),
                H("Logarithmic error for either sign"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For natural numbers 1 ≤ A ≤ B and a real multiplier s with |s| ≤ 1, "
                        + "let Q be the sum of the weighted positive parts of the affine chords of sU "
                        + "between consecutive fourth powers from A⁴ to B⁴. The weight is x^(−3/2). "
                        + "The absolute difference between Q and the weighted positive mass of sU "
                        + "is at most 4275(log B − log A) + 3375/A + 225(log 4 + 6).")),
                    Paragraph(Text(
                        "An arithmetic hinge contributes to the interpolation error only when its knot "
                        + "lies strictly inside the cell. Integrating the cell error charges at most "
                        + "3375/n for the logarithmic curvature and 225 times the sum of Λ(k)/k over "
                        + "the interior knots. The harmonic sum and the weighted Mangoldt sum give the "
                        + "uniform logarithmic bound."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("off-line-zero-forces-signed-quartic-chord-mass"),
                DeclarationHandle.Create(Owner + "off_line_zero_forces_signed_quartic_chord_mass"),
                H("Power growth on every sufficiently late block"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "If ζ has a zero with real part β > 1/2, then for each ε > 0, on every "
                        + "sufficiently late block of fourth powers with indices from k³ to k⁴, "
                        + "each signed chord mass is at least k^(16(β − 1/2) − ε). "
                        + "The same threshold in k works for both signs.")),
                    Paragraph(Text(
                        "The complete Chebyshev tail identity identifies the signed integral with "
                        + "the continuous mass in the existing pole-growth theorem. The latter is "
                        + "applied on the power window from k¹² to k¹⁶ with a smaller exponent loss. "
                        + "That smaller loss absorbs the logarithmic chord error."))),
                DescribeRole.Theorem))));
}

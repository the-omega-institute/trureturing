using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Laplace;

internal sealed class ExponentialMultiplierContourDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/Laplace/ExponentialMultiplierContour.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Vertical contour shifting under polynomial decay after exponential smoothing.",
        H("Exponential multiplier contour shift"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("smoothed"),
                DeclarationHandle.Create(Prefix + "smoothed"),
                H("Smoothed inversion integrand"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For real σ, c, t, a complex function F, and a complex point z, "
                    + "the integrand is exp((z − σ)t) F(z) c/(c + z − σ)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("smoothed-vertical-shift"),
                DeclarationHandle.Create(Prefix + "smoothed_vertical_shift"),
                H("Absolute convergence and vertical shift"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let σ < σ₀, c > 0, C ≥ 0, and p > 0. Assume F is complex "
                    + "differentiable at every point of the closed strip with real parts "
                    + "in [σ, σ₀], and that |F(a + iy)| ≤ C(1 + |y|)^(−p) for every "
                    + "a in [σ, σ₀] and real y. For each real t, every vertical section "
                    + "of the smoothed integrand on the strip is integrable in y. Its "
                    + "integral in a from σ to σ₀ tends to zero as y tends to either "
                    + "positive or negative infinity. The full integrals in y on the two "
                    + "boundary lines are equal."))),
                DescribeRole.Theorem))));
}

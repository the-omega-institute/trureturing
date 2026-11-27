using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.NullConeGravity;

internal sealed class NullDiamondBesselSeries4DDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselSeries4D.";

    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HilbertOperators/satishchandransorce2026nulllocal");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Entire power series and the mixed derivative of the four-dimensional null-diamond bulk difference.",
        H("Logarithmic power series for the null-diamond correction"),
        Blocks(
            Paragraph(Text("For the four-dimensional scalar covariance problem of Satishchandran and Sorce, "
                + "the bulk difference combines two entire power series and a principal logarithm. "
                + "Differentiating the product of the null radii times that difference gives the weighted series "
                + "of the correction.")),
            Entry("factorial-coefficient", "pk", "Factorial coefficient",
                "For each natural k, pₖ = 1/(k!(k+1)!), viewed as a complex number.", DescribeRole.Definition),
            Entry("harmonic-coefficient", "bk", "Harmonic coefficient",
                "For each natural k, bₖ = Hₖ + Hₖ₊₁ − 2γ, where H denotes the harmonic numbers "
                + "and γ is the Euler–Mascheroni constant. The coefficient takes values in ℂ.", DescribeRole.Definition),
            Entry("power-series", "besselP", "Factorial power series",
                "For complex t, P(t) is the sum over natural k of pₖ tᵏ.", DescribeRole.Definition),
            Entry("harmonic-series", "besselB", "Harmonic-weighted power series",
                "For complex t, B(t) is the sum over natural k of bₖ pₖ tᵏ.", DescribeRole.Definition),
            Entry("weighted-power-series", "besselP2", "Quadratically weighted factorial series",
                "For complex t, P₂(t) is the sum over natural k of (k+1)² pₖ tᵏ.", DescribeRole.Definition),
            Entry("weighted-harmonic-series", "besselB2", "Quadratically weighted harmonic series",
                "For complex t, B₂(t) is the sum over natural k of ((k+1)² bₖ − 2(k+1)) pₖ tᵏ.",
                DescribeRole.Definition),
            Entry("bulk-difference", "bulkDifference", "Bulk difference",
                "For real M and complex q, put t = M²q/4. The bulk difference is "
                + "M²/(16π²) times (log(t) P(t) − B(t)), with the principal complex logarithm.",
                DescribeRole.Definition),
            Entry("correction-log", "correctionLog", "Correction with a supplied logarithm",
                "For real M and complex t and ℓ, the correction with logarithm ℓ is "
                + "M²/(16π²) times (ℓ P₂(t) − B₂(t)).", DescribeRole.Definition),
            Entry("boundary-correction", "correction", "Boundary correction",
                "For real M, u, v and x with x < 1, take t = M²uv(1−x)/2 and use the real "
                + "logarithm of t, embedded in ℂ, in the correction with a supplied logarithm. "
                + "The correction is zero for x ≥ 1.", DescribeRole.Definition),
            Entry("entire-factorial-series", "besselP_entire", "The factorial series is entire",
                "P is complex differentiable on ℂ. On each bounded disk a factorial majorant controls "
                + "the series of derivatives."),
            Entry("entire-harmonic-series", "besselB_entire", "The harmonic-weighted series is entire",
                "B is complex differentiable on ℂ. The harmonic numbers grow at most linearly, so their "
                + "weights still admit a locally uniform factorial majorant."),
            Entry("entire-weighted-factorial", "besselP2_entire", "The weighted factorial series is entire",
                "P₂ is complex differentiable on ℂ. The quadratic weight preserves the local summability "
                + "of the derivative majorant."),
            Entry("entire-weighted-harmonic", "besselB2_entire", "The weighted harmonic series is entire",
                "B₂ is complex differentiable on ℂ. Split it into the quadratically weighted harmonic "
                + "series and twice the linearly weighted factorial series."),
            Entry("normalized-series", "besselSeries", "Normalized logarithmic series",
                "For real t, the normalized series F(t) is 1 + t(log(t) P(t) − B(t)), where log is "
                + "the real logarithm and all values are combined in ℂ.", DescribeRole.Definition),
            Entry("series-slope", "besselSeriesSlope", "Logarithmic series for the first derivative",
                "For real t, the slope series is log(t) P₁(t) + P(t) − B₁(t), where P₁ and B₁ "
                + "are the series P and B with each coefficient multiplied by k+1.",
                DescribeRole.Definition),
            Entry("derivative-of-normalized-series", "hasDerivAt_besselSeries", "First derivative of the normalized series",
                "At every real t > 0, the real derivative of the complex-valued F is the slope series. "
                + "Differentiate the logarithm and the two power series term by term."),
            Entry("derivative-of-series-slope", "hasDerivAt_besselSeriesSlope", "Differential equation for the series",
                "At every real t > 0, the real derivative of the complex-valued slope series is F(t)/t. "
                + "The recurrence of successive factorial coefficients and harmonic numbers gives the coefficient identities."),
            Entry("normalized-series-at-zero", "tendsto_besselSeries_zero", "Right limit of the normalized series",
                "F(t) tends to 1 as real t decreases to zero. Use continuity of the two entire series "
                + "and the vanishing of t log(t)."),
            Entry("series-slope-at-zero", "tendsto_besselSeriesSlope_sub_log", "Right limit of the regularized slope",
                "The slope series minus log(t) tends to 2γ as real t decreases to zero. "
                + "The difference P₁(t) − 1 vanishes to first order, and B₁(0) = 1 − 2γ fixes the limit."),
            Entry("correction-as-series-and-slope", "correctionLog_eq_series", "Correction as series plus slope",
                "For real M and t, the correction at the real logarithm of t equals M²/(16π²) "
                + "times the sum of the normalized series and its slope series. "
                + "Compare the weighted factorial and harmonic coefficients."),
            Entry("mixed-derivative", "correction_mixed_deriv", "Mixed derivative in the null radii",
                "For real M, u and v positive and real x < 1, take the u derivative and then the v derivative "
                + "of uv times the bulk difference at q = 2uv(1−x). Both derivatives are real and take values "
                + "in ℂ. The resulting mixed derivative is the boundary correction at M, u, v and x."))));

    private static DocumentBlock Entry(string id, string declaration, string title, string statement,
        DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(statement))), role);
}

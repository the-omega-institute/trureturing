using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy.RenyiCombining;

internal sealed class CachinShannonBranchDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Entropy/RenyiCombining/CachinShannonBranch.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Shannon elasticity is strictly increasing, so its multiplicative slope ratios are strictly decreasing.",
        H("Shannon Elasticity Certificate"),
        Blocks(
            Paragraph(Text("This module treats alpha = 1 directly using natural-log binary entropy. "
                + "The pinned Mathlib defines artanh by a logarithm and supplies its positivity and half-log representation. "
                + "The derivative is obtained from that representation locally on (-1,1). "
                + "No limiting identification with the non-Shannon power formula is used.")),
            Node("E", "Shannon elasticity", "E(t) = t / ((1-t^2) artanh(t))", DescribeRole.Definition,
                "The defining expression is a total real function. Its derivative and sign arguments use 0 < t < 1."),
            Node("artanh_hasDerivAt", "Derivative of inverse hyperbolic tangent",
                "-1 < t < 1 → HasDerivAt artanh (1/(1-t^2)) t", DescribeRole.Theorem,
                "The half-log formula and the quotient and logarithm derivative rules give the derivative."),
            Node("self_le_artanh", "A lower bound for inverse hyperbolic tangent",
                "0 < t < 1 → t ≤ artanh(t)", DescribeRole.Theorem,
                "The derivative of artanh(t)-t is nonnegative on [0,t], and its value at zero is zero."),
            Node("E_hasDerivAt", "Derivative of Shannon elasticity",
                "0 < t < 1 → HasDerivAt E (((1+t^2)artanh(t)-t)/((1-t^2)artanh(t))^2) t", DescribeRole.Theorem,
                "The quotient rule gives the derivative. Its numerator is positive because artanh(t) >= t and t^2 artanh(t) > 0."),
            Node("E_strictMonoOn", "Strict monotonicity of Shannon elasticity",
                "StrictMonoOn E (Ioo 0 1)", DescribeRole.Theorem,
                "The derivative is strictly positive throughout the interval. The real mean value theorem gives strict monotonicity."),
            Node("slope_ratio_strictAntiOn", "Strict decrease of Shannon slope ratios",
                "0 < v < 1 → StrictAntiOn (t ↦ v artanh(vt)/artanh(t)) (Ioo 0 1)", DescribeRole.Theorem,
                "The derivative factors as v artanh(vt)/(t artanh(t)) times E(vt)-E(t). "
                + "Its first factor is positive and its second factor is negative. This is the slope comparison consumed by entropy-coordinate convexity."),
            Node("binEntropy_bias_hasDerivAt", "Derivative of binary Shannon entropy in bias coordinates",
                "0 < t < 1 → HasDerivAt (s ↦ binEntropy((1-s)/2)) (-artanh(t)) t", DescribeRole.Theorem,
                "Mathlib's binary entropy derivative and the affine change of coordinates give minus artanh(t). "
                + "This supplies the Shannon branch independently of the real-power derivative formulas."))));

    private static DocumentBlock Node(string name, string title, string formula, DescribeRole role, string prose) =>
        Describe.Lean(DescribeId.Create("cachin-shannon-" + name.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromLean(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(formula)), Paragraph(Text(prose))), role);
}

using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaExplicit;

internal sealed class SixthPowerSamplingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The convexity barrier for sixth-power sampling",
        H("One common convex interpolant"),
        Blocks(Describe.Lean(
            DescribeId.Create("sixth-power-convex-sampling-countermodel"),
            DeclarationHandle.Create(
                "D5/S3/Weil/ZetaExplicit/SixthPowerSampling.sixth_power_convex_sampling_countermodel"),
            H("Exact samples and growing midpoint deviations"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "There exists a single function H from the real numbers to the real numbers, "
                    + "convex on the entire real line, such that for every natural n at least one, "
                    + "H(n⁶) = n⁶ log(n⁶). Put m = (n⁶ + (n+1)⁶)/2. The same function satisfies "
                    + "H(m) - m log(m) ≥ (9/1024)n√m for every such n.")),
                Paragraph(Text(
                    "Write g(x) = x log(x). For each adjacent pair of positive sixth powers, "
                    + "extend the secant of g to an affine function on the whole real line. "
                    + "Define H as the supremum of all these affine functions. At any sample point "
                    + "every secant extension lies below g: the sample is outside that secant's open cell, "
                    + "so the assertion follows from convexity of g. The corresponding secant attains "
                    + "equality. All slopes are nonnegative; a sample point to the right of any given "
                    + "real x therefore bounds every secant at x. The supremum is finite and convex.")),
                Paragraph(Text(
                    "On an interval [a,b] with 0 < a ≤ b, the function b g(x) - x²/2 is convex, "
                    + "because its second derivative is b/x - 1 ≥ 0. Its midpoint inequality gives "
                    + "b((g(a)+g(b))/2 - g((a+b)/2)) ≥ (b-a)²/8. Taking a = n⁶ and b = (n+1)⁶, "
                    + "one has b-a ≥ 6n⁵, b ≤ 64n⁶ and √m ≤ 8n³. Since H dominates that secant, "
                    + "its midpoint deviation is at least (9/128)n⁴, hence at least (9/1024)n√m.")),
                Paragraph(Text(
                    "Thus convexity and exact sixth-power samples alone do not control a fixed "
                    + "square-root envelope between samples: the displayed lower bound has an "
                    + "unbounded coefficient. This is an abstract convexity obstruction. It makes "
                    + "no claim that the actual von Mangoldt ramp sum has these deviations. "
                    + "The actual fourth-power sampling criterion uses the finer mesh; further "
                    + "sparsification must exploit additional information about the arithmetic weights."))),
            DescribeRole.Theorem))));
}

using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Laplace;

internal sealed class CausalExponentialStripTransferDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/Laplace/CausalExponentialStripTransfer.";

    private static DocumentBlock.Describe DescribeSource(string id, string name, string title, string statement,
        DescribeRole role) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + name),
            H(title),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(statement))),
            role);

    private const string StripHypotheses =
        "Let σ < σ₀, C ≥ 0, and p > 0. Assume F is complex differentiable at "
        + "every point of the closed strip [σ, σ₀] and |F(a + iy)| ≤ "
        + "C(1 + |y|)^(−p) for every a in [σ, σ₀] and real y. Assume the tilt "
        + "of g by σ₀ − σ is integrable and its Fourier transform equals "
        + "the section of F at σ₀ as a function. Assume the section at σ belongs to L². ";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Transfer of square integrability from a Fourier section to a causal function.",
        H("Causal exponential strip transfer"),
        Blocks(
            DescribeSource("kernel", "kernel", "Causal exponential kernel",
                "For real c, a, and s, the kernel is c exp(−as) for s ≥ 0 and "
                + "zero for s < 0, with values included in the complex numbers.",
                DescribeRole.Definition),
            DescribeSource("multiplier", "multiplier", "Fourier multiplier",
                "For real c, a, and ξ, the multiplier is c/(a + 2πiξ).",
                DescribeRole.Definition),
            DescribeSource("smoothing", "smoothing", "Causal smoothing",
                "For real c and complex-valued g on the real line, smoothing is convolution "
                + "of g with the causal kernel of amplitude and rate c.",
                DescribeRole.Definition),
            DescribeSource("tilt", "tilt", "Exponential tilt",
                "For real d and complex-valued g on the real line, the tilt at time t "
                + "is exp(−dt) g(t).",
                DescribeRole.Definition),
            DescribeSource("section-at", "sectionAt", "Normalized vertical section",
                "For complex F and real a and ξ, the section at a evaluated at ξ is "
                + "F(a + 2πiξ).",
                DescribeRole.Definition),
            DescribeSource("fourier-kernel", "fourier_kernel", "Transform of the kernel",
                "For every real amplitude c, positive rate a, and real frequency ξ, "
                + "the Fourier transform of the causal kernel at ξ is c/(a + 2πiξ).",
                DescribeRole.Theorem),
            DescribeSource("integrable-old-line-integrand", "integrable_oldLine_integrand",
                "Absolute integrability of the old-line convolution",
                "For c ≥ 0, a > 0, and integrable g₀, the function "
                + "s ↦ kernel(c, a, s) g₀(t − s) is integrable for each real t.",
                DescribeRole.Theorem),
            DescribeSource("old-line-smoothing-eq-fourier-inv", "oldLineSmoothing_eq_fourierInv",
                "Pointwise inversion on the old line",
                "For c ≥ 0 and a > 0, assume g₀ is integrable and its Fourier transform "
                + "times the multiplier c/(a + 2πiξ) is integrable. The convolution of "
                + "the causal kernel with g₀ equals the inverse Fourier transform of "
                + "that product as a function.",
                DescribeRole.Theorem),
            DescribeSource("integrable-smoothing-integrand", "integrable_smoothing_integrand",
                "Absolute integrability with a bounded past",
                "Let c > 0 and let g be measurable. If |g(x)| ≤ M for every x ≤ t, "
                + "then s ↦ kernel(c, c, s) g(t − s) is integrable.",
                DescribeRole.Theorem),
            DescribeSource("smoothing-tendsto-at-top", "smoothing_tendsto_atTop",
                "Convergence at continuity points",
                "If g is measurable, continuous at t, and satisfies |g(x)| ≤ M for "
                + "all x ≤ t, its causal exponential smoothing at t tends to g(t) "
                + "as c tends to positive infinity.",
                DescribeRole.Theorem),
            DescribeSource("smoothing-transfer", "smoothing_transfer", "Transfer at a fixed rate",
                StripHypotheses
                + "For each c > 0, the smoothing of g equals the pointwise inverse "
                + "Fourier transform of the target section multiplied by c/(c + 2πiξ). "
                + "The smoothing belongs to L² and its extended L² norm is bounded by "
                + "that of the target section.",
                DescribeRole.Theorem),
            DescribeSource("mem-lp-of-strip-transfer", "memLp_of_strip_transfer",
                "L² membership after removing the smoothing",
                StripHypotheses
                + "Suppose further that g is measurable, continuous almost everywhere, "
                + "vanishes at negative times, and is bounded on each interval [0, T]. "
                + "Then g belongs to L². The smoothing converges almost everywhere "
                + "along the positive integer rates, and the fixed-rate L² bound "
                + "passes to the limit.",
                DescribeRole.Theorem))));
}

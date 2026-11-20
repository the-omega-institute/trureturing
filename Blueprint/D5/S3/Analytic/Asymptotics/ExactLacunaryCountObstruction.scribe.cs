using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Asymptotics;

internal sealed class ExactLacunaryCountObstructionDocument : IScribeDocumentDefinition
{
    private const string Gid = "D5/S3/Analytic/Asymptotics/ExactLacunaryCountObstruction";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact lacunary series cannot equal a weighted monotone-count primitive on a tail.",
        H("A monotone-count obstruction for the exact lacunary series"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("no-monotone-tail-realization"),
                DeclarationHandle.Create(Gid + ".no_monotone_tail_realization"),
                H("The exact model has no monotone tail realization"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let β be a real sequence indexed by n ≥ 0 with 1/2 ≤ β(n) ≤ 1. "
                        + "Put γ(n) = 3^(n+1), ρ(n) = β(n) + iγ(n), and "
                        + "c(n) = 1/(ρ(n)(1−ρ(n))). Define modelSeries(β,t) as "
                        + "−2 times the sum over n of exp((β(n)−1)t) times "
                        + "(Re(c(n)) cos(γ(n)t) − Im(c(n)) sin(γ(n)t)).")),
                    Paragraph(Text(
                        "There are no real-valued functions V and k on ℝ and real T satisfying all "
                        + "of the following conditions. The function V is nondecreasing on [exp(T),∞). "
                        + "For every real a,b with 0 < a, T ≤ a, and a ≤ b, the function "
                        + "v ↦ q(v)r(V,v) is interval integrable with respect to volume on a..b, and "
                        + "k(b) − k(a) equals its integral from a to b. Here q(v) = (v+1)/v² and "
                        + "r(V,v) = 1 − exp(−v)V(exp(v)). Finally, t k(t) = modelSeries(β,t) "
                        + "for all sufficiently large real t.")),
                    Paragraph(Text(
                        "Take a center t₀ = 2πm with m integral and t₀−1 above the positive-time, "
                        + "monotonicity and eventual-equality thresholds. The finite curvature "
                        + "bound on [t₀−1,t₀+1] gives one upper bound C for the central second "
                        + "difference of t k(t) at t₀ divided by h² for 0 < h < 1. "
                        + "Each γ(n)t₀ is an integral multiple of 2π. After shifting by t₀, "
                        + "the weights are exp((β(n)−1)t₀)Re(c(n)) and "
                        + "exp((β(n)−1)t₀)Im(c(n)). The first weights are nonnegative and summable "
                        + "with divergent second moment, while the second weights and their "
                        + "first frequency moment are absolutely summable. Common-phase "
                        + "spectral curvature makes the same normalized difference tend to "
                        + "+∞ as h approaches zero through nonzero values. For some 0 < h < 1 "
                        + "it is at least C+1, contradicting the count bound."))),
                DescribeRole.Theorem))));
}

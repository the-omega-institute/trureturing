using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower;

internal sealed class MobiusWindowTransferDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Transfer a pointwise density bound to a prime window",
        H("Integrate over the original endpoints"),
        Blocks(
            Paragraph(Text("Assume RH and fix K > 0. For each integer m ≥ 2, put s(m) = 1/2 − 1/(m+1). "
                + "Let F(m,u) be the sum of retained(m,n,u) over 2 ≤ n ≤ m. For every u ≥ log 2, "
                + "assume |rootWindowDensity(u) − (F(m,u) − 2)| ≤ K × factor(m) × exp(−s(m)u). "
                + "At u = log 2 the left side is nonnegative and K and the exponential are positive, "
                + "so factor(m) ≥ 0.")),
            Paragraph(Text("For m ≥ 2, integer indices 2 ≤ n ≤ m and real endpoints 2 ≤ a ≤ B, "
                + "retained(m,n,·) is interval integrable against Lebesgue measure from log a to log B. "
                + "Its integral is the sum of an arithmetic term and a spectral term. The arithmetic "
                + "term is 2(log B − log a) for n = 2, and otherwise it is "
                + "−μ(n) × 2n²/((n−1)(n−2)) × (a^(1/n−1/2) − B^(1/n−1/2)). "
                + "The spectral term is −μ(n) × (rootPrimitive(n,B) − rootPrimitive(n,a)) "
                + "when 2n < m+1 and zero otherwise. The law includes B = a.")),
            Paragraph(Text("Choose the lower threshold from the eventual positive negative-tail mass. "
                + "Transport its integral to the original log window. Summing the retained primitives gives "
                + "the endpoint differences. The integral of exp(−s(m)u) is the endpoint power gap divided "
                + "by s(m). Since s(m) is at least one sixth, the absolute window residual is bounded "
                + "by 6K × factor(m) × (a^(−s(m)) − B^(−s(m))).")))));
}

using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder;

internal sealed class LateArithmeticTailDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The arithmetic Möbius tail at late starting points",
        H("Split the omitted degrees at twice the cutoff"),
        Blocks(
            Paragraph(Text("For q=m+1 and u≥q^(3/2), the absolute normalized arithmetic tail "
                + "beyond m is bounded by C(1+q²/u) exp(−(1/2−1/q)u), with one positive C "
                + "for all m≥2 and real u with exp(u)≥2.")),
            Paragraph(Text("In the pointwise Chebyshev sum, isolate the degrees q through 2q−1. "
                + "Their normalized powers are bounded by a geometric sum with ratio "
                + "exp(−log(t)/(2q²)). The existing truncation at 2q−1 bounds higher degrees, "
                + "whose contribution relative to the first omitted power has damping "
                + "exp(−log(t)/(2q)).")),
            Paragraph(Text("For q>0 and u≥q^(3/2), the quadratic bound for the exponential gives "
                + "q exp(−u/(2q))≤8. Integrating the pointwise estimate for t>exp(u) uses "
                + "1+q²/log(t)≤1+q²/u.")))));
}

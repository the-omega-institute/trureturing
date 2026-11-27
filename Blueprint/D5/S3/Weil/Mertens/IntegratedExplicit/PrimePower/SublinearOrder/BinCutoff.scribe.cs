using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder;

internal sealed class BinCutoffDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Quantitative bounds for the symmetric bin cutoff",
        H("Finite head and infinite square tail"),
        Blocks(
            Paragraph(Text("Split the signed bins into the nonnegative and negative sides. The finite sum of (1+|k|) to the power −3/4 is bounded by eight times the fourth root of one plus the cutoff. Outside the cutoff H>0, the sum with exponent −3/2 is bounded by four times H to the power −1/2.")),
            Paragraph(Text("For log root cutoff at least L times the order scale, choose the integer bin cutoff to be the ceiling of L². The fourth-root growth in the finite sum is offset by the geometric degree weights. The square tail supplies the same inverse-square-root decay in L.")),
            Paragraph(Text("Taking L=(1+log log(m+1))/8 also controls the arithmetic terms at large order. Its exponential enters the near-range Abel bound.")))));
}

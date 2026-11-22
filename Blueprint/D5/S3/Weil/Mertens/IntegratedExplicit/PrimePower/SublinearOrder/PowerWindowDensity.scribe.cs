using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder;

internal sealed class PowerWindowDensityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Power-weighted prime-window density",
        H("Combination of the signed responses"),
        Blocks(
            Paragraph(Text("For a prefix estimate of order q^β, the signed arithmetic tail and near centered response "
                + "have coefficients of order q^β. The signed trivial-root term has an extra 1+log q factor.")),
            Paragraph(Text("If the far omitted-root sum has coefficient q^κ with κ>β, the trivial-root logarithm "
                + "is absorbed by the slack κ−β. Each contribution has the same exponential density factor.")))));
}

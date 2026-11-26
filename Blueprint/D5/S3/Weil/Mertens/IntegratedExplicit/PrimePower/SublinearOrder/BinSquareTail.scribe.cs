using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder;

internal sealed class BinSquareTailDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Power tails of symmetric frequency bins",
        H("The tail for negative exponents"),
        Blocks(
            Paragraph(Text("For real s<−1 and integer H>0 the sum of (1+|k|)^s over |k|>H is at most "
                + "2 H^(s+1)/(−s−1). Split the integers by sign and compare each shifted tail "
                + "with the integral of the decreasing real power.")))));
}

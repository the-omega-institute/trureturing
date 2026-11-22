using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.LinearOrder;

internal sealed class TrivialResponseDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed sums of trivial-zero root responses",
        H("Möbius cancellation in the degree sum"),
        Blocks(
            Paragraph(Text("Abel summation of the signed degree weights uses the uniform Möbius prefix bounds. The uniform little-o prefix bound gives a sublinear trivial-root response.")),
            Paragraph(Text("At log cutoff u≥0 the jth trivial zero contributes n/[2j(n+2j)] times exp(−2ju/n). This response is nonnegative, increases with n, and is at most half of one plus log n. Abel summation uses the shorter-prefix bound and controls the signed weighted sum.")),
            Paragraph(Text("The exact centered root formula includes the constant −log(2π). Its contribution and the summed response are bounded by a constant times m exp(−u/2).")))));
}

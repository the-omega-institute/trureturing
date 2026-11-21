using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower;

internal sealed class MobiusWindowTransferDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Transfer a pointwise density bound to a prime window",
        H("Integrate over the original endpoints"),
        Blocks(
            Paragraph(Text("Assume RH, a nonnegative factor for each truncation order m, and a pointwise "
                + "bound by K times that factor times exp(−s(m)u) for the signed log-density residual. "
                + "The retained densities are integrable and their primitives supply the arithmetic powers "
                + "and the selected root spectra.")),
            Paragraph(Text("Choose the lower threshold from the eventual positive negative-tail mass. "
                + "Transport its integral to the original log window. Summing the retained primitives gives "
                + "the endpoint differences. The integral of exp(−s(m)u) is the endpoint power gap divided "
                + "by s(m). Since s(m) is at least one sixth, the residual is bounded by six times K and "
                + "the same factor times the gap. The argument includes equal endpoints.")))));
}

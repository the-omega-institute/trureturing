using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower;

internal sealed class MobiusWindowTransferDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Transfer a pointwise density bound to a prime window",
        H("Integrate over the original endpoints"),
        Blocks(
            Paragraph(Text("Assume RH. For any m≥2 put s(m)=1/2−1/(m+1). "
                + "Let C exp(−s(m)u) bound the absolute signed log-density residual for log a≤u≤log B. "
                + "For ordered endpoints 2≤a≤B the integrals of the retained densities give "
                + "the signed arithmetic powers and the selected root spectra.")),
            Paragraph(Text("The eventual sign of the prime-only tail gives one lower threshold "
                + "for all orders and coefficients C. Integrating on [log a,log B] multiplies "
                + "the endpoint power gap by C/s(m). Since s(m)≥1/6, six times C gives "
                + "the claimed bound. The equal-endpoint window is included. The uniform version applies when the density estimate holds for every u≥log 2.")))));
}

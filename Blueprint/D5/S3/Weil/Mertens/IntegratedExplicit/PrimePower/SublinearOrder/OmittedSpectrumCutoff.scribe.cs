using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder;

internal sealed class OmittedSpectrumCutoffDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed omitted-root frequency cutoffs",
        H("Degree cancellation and weighted sampling"),
        Blocks(
            Paragraph(Text("Below the cutoff, complex Abel summation takes the Möbius sum over degrees first. "
                + "The weighted adjacent-phase increment is paid for by the decrease of the exponential "
                + "envelope, giving a degree variation bound uniform in u.")),
            Paragraph(Text("Above the cutoff, a square sum of inverse-root bin masses controls the separated "
                + "samples u/n. The two bounds hold on the same finite occurrence set. Summability "
                + "at each degree extends the bound to the series with analytic multiplicities.")))));
}

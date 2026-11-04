using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle;

internal sealed class ThreeNegativeMinimumTwoMasksDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact masks for the minimum-two physical constructor", H("Private arithmetic of the physical constructor"),
        Blocks(Paragraph(Text("The private constructor specifies thirty rows: seven axes, five rows with a=2, five with b=2, and thirteen with c=2. Its masks select physical U,V,W labels by set bits. Capacities are t/2,s/2,r/2; P and T are disjoint within each chain, and Q is the physical complement. The dyadic rows use exact shifted bit-disjointness and retain every small-coordinate exception. These certificates are consumed by the one complete minimum-two joint-lift theorem."))), []));
}

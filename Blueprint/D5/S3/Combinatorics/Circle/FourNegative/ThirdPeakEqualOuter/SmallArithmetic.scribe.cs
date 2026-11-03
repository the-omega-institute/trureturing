using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualOuter;
internal sealed class SmallArithmeticDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Unbounded small-b residue selectors", H("Original labels and exact unbounded domain"),
        Blocks(Paragraph(Text("Three parameter families are represented by (b,c-a)=(2,1),(2,2),(3,2). Their fixed dyadic y,m values leave s=2^(a-b) unbounded. Exact residue bounds and selector certificates prove the after-W windows above the family thresholds; this is a proof for all qualifying s rather than finite enumeration of exponents."))), []));
}

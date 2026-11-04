using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2AllH;
internal sealed class AllSelectionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Unbounded a2 AllSelection", H("Unbounded a2 AllSelection"),
        Blocks(Paragraph(Text("For every u>=2, s>=1 and every natural k, construct Good (2^u) (2^s) (2^k). The cases k<=1 use the original dyadic selector, p=4,8,16,32 use the existing unbounded small selector, and p>=64 uses the large selector. No upper exponent bound or selector hypothesis occurs."))), []));
}

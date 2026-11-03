using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualOuter;
internal sealed class LargeThirdDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Unbounded large-third equal-outer branch", H("Original labels and exact unbounded domain"),
        Blocks(Paragraph(Text("For c>=a+3 set s=2^(a-b),y=2^b,m=2^(c-a), x=sy,z=mx. Then s>=2,y>=4,m>=8. The integer floor selector v=floor((4s-1)A/(2SU))+1 satisfies 1<=v<sm and all after-W windows. The masks are converted to natural stocks with explicit capacity bounds and fed to afterW_realize."))), []));
}

using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakLargeThird;
internal sealed class DiagonalMasksDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal paid bit in the original V stock", H("Original labels and exact unbounded domain"),
        Blocks(Paragraph(Text("For every a,c put p=0 if c<=3a+1, otherwise p=2^(c-3a-2). In the paid branch p=2^r, the exact decomposition v=2^r(2x^2-1)+q with q<2^r and odd coefficient proves testBit(v,r)=true. Thus p is a genuine submask of v. A numerical inequality p<=v is insufficient and is not used as a containment argument."))), []));
}

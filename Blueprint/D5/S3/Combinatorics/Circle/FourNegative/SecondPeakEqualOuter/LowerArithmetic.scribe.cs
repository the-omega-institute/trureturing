using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualOuter;
internal sealed class LowerArithmeticDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "All lower endpoint windows", H("Physical construction"),
        Blocks(Paragraph(Text("Assume 2<=c<a<b. Write s=2^(a-c),h=2^(b-a-1),x=sz,y=2xh. Twenty-two integer polynomial inequalities follow by shifts to nonnegative variables and ring normalization. They cover s=2 or s=4q, and h=1,2 or h>=4. With r=ceil((K-L)/(2L)), t=2 if s=2 and t=3s/4 otherwise, u=r if s=2 and zero otherwise, the doubled old seams are A-K, A-K+2B-2tA+2uL, (2r+1)L-K. New seams are 3A-SW, (3-4t)A-SW+2SU+2uSV, (2r+1)SV-SW. Each lies between zero and its actual terminal head minus one."))), []));
}

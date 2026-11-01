using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.SecondPeakIndependentTailInterior;
internal sealed class Chart0Document : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform even rounding", H("Endpoint positivity in the rounding coordinate"),
        Blocks(Paragraph(Text("For t=2(T+1), set D0=(T+1)(w+3z+2)/4-(K-1)/2 and W0=Kq-1. The two charts use z=4 or z=Z+8, w=4z(V+1), q=R+1 and u=2(V+1)-1 or 2(V+1). Every seam and peak slack at K=1 and K=4 is an explicit polynomial with nonnegative coefficients in the nonnegative coordinates Z,V,T,R divided by a positive integer. Exact polynomial identities include both final zero seams. Affinity in K gives the bound throughout 1<=K<=4 by the weights (4-K)/3 and (K-1)/3."))), []));
}

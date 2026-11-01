using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.SecondPeakIndependentTailInterior;
internal sealed class ParametersDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Independent low-bit coordinates", H("The full four-parameter domain"),
        Blocks(Paragraph(Text("The private parameter structure retains independent naturals a,b,c,d with c>=2, d>=c+2, a>=c+d and b>=a+1. Subtraction defines r=a-c-d, s=b-a-1 and v=d-c-2. The exact exponent decompositions give w=4z2^v, x=tz w and y=2qx, where z=2^c, w=2^d, t=2^r and q=2^s. Zero r,s,v are included."))), []));
}

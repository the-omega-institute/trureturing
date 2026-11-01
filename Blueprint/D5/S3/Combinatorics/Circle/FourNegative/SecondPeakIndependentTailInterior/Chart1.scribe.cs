using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.SecondPeakIndependentTailInterior;
internal sealed class Chart1Document : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The boundary t=1", H("Three c cases and the half-unit floor error"),
        Blocks(Paragraph(Text("At t=1, the three charts use z=4, z=8, or z=Z+16, with w=4z(V+1) and q=R+1. Their D0 coordinates are w/8, w/8+2, and (w+3z)/8. Their W0 coordinates are 4q-1, 7q/2-1-eps, and 3q/2-1-eps. Here eps is zero or one half for the actual dyadic q. Every seam and peak slack at both eps endpoints is a polynomial with nonnegative coefficients in Z,V,R divided by a positive integer; the z=4 expressions are independent of eps. All terminal-zero seams and final peak slacks are included. The expressions are affine in eps, so the endpoint bounds also hold between the two endpoints."))), []));
}
